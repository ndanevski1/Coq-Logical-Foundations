(** * Tactics: More Basic Tactics *)

(** This chapter introduces several additional proof strategies
    and tactics that allow us to begin proving more interesting
    properties of functional programs.  We will see:

    - how to use auxiliary lemmas in both "forward-style" and
      "backward-style" proofs;
    - how to reason about data constructors (in particular, how to use
      the fact that they are injective and disjoint);
    - how to strengthen an induction hypothesis (and when such
      strengthening is required); and
    - more details on how to reason by case analysis. *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Poly.

(* ################################################################# *)
(** * The [apply] Tactic *)

(** We often encounter situations where the goal to be proved is
    _exactly_ the same as some hypothesis in the context or some
    previously proved lemma. *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.

(** Here, we could finish with "[rewrite -> eq2.  reflexivity.]" as we
    have done several times before.  We can achieve the same effect in
    a single step by using the [apply] tactic instead: *)

  apply eq2.  Qed.

(** The [apply] tactic also works with _conditional_ hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved. *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** Typically, when we use [apply H], the statement [H] will
    begin with a [forall] that binds some _universal variables_.  When
    Coq matches the current goal against the conclusion of [H], it
    will try to find appropriate values for these variables.  For
    example, when we do [apply eq2] in the following proof, the
    universal variable [q] in [eq2] gets instantiated with [n] and [r]
    gets instantiated with [m]. *)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** **** Exercise: 2 stars, standard, optional (silly_ex)  

    Complete the following proof without using [simpl]. *)

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     oddb 3 = true ->
     evenb 4 = true.
Proof.

intros n eq1.
apply eq1.
Qed.
(** [] *)

(** To use the [apply] tactic, the (conclusion of the) fact
    being applied must match the goal exactly -- for example, [apply]
    will not work if the left and right sides of the equality are
    swapped. *)

Theorem silly3_firsttry : forall (n : nat),
     true = (n =? 5)  ->
     (S (S n)) =? 7 = true.
Proof.
  intros n H.

(** Here we cannot use [apply] directly, but we can use the [symmetry]
    tactic, which switches the left and right sides of an equality in
    the goal. *)

  symmetry.
  simpl. (** (This [simpl] is optional, since [apply] will perform
             simplification first, if needed.) *)
  apply H.  Qed.

(** **** Exercise: 3 stars, standard (  apply_exercise1)  

    (_Hint_: You can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [Search] is
    your friend.) *)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.

Search rev. (* as given in the hint we need the lemmas/theorems for rev *)
intros l l' eq.
rewrite eq.
symmetry.
apply rev_involutive. (* apply the most important function for rev *)

Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (apply_rewrite)  

    Briefly explain the difference between the tactics [apply] and
    [rewrite].  What are the situations where both can usefully be
    applied? *)

(* FILL IN HERE 
  I think that the usage of rewrite is more simbolic. 
It will only rewrite one side of our equation with something else and it is
up to us to continue working.
Apply will use an already proven (or given) property and modify
(possibly both sides) of what we want to prove by following a forward or 
backward method of proving. An advantage of apply (as stated in the book) 
is that it can be used to instantiate a claim (lemma/theorem) that we know 
to be true for generic variables.
As given in the first exercise, both can be used in a case when we have
equality on both sides.
     *)

(* ################################################################# *)
(** * The [apply with] Tactic *)

(** The following silly example uses two rewrites in a row to
    get from [[a;b]] to [[e;f]]. *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** Since this is a common pattern, we might like to pull it out
    as a lemma recording, once and for all, the fact that equality is
    transitive. *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

(** Now, we should be able to use [trans_eq] to prove the above
    example.  However, to do this we need a slight refinement of the
    [apply] tactic. *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.

(** If we simply tell Coq [apply trans_eq] at this point, it can
    tell (by matching the goal against the conclusion of the lemma)
    that it should instantiate [X] with [[nat]], [n] with [[a,b]], and
    [o] with [[e,f]].  However, the matching process doesn't determine
    an instantiation for [m]: we have to supply one explicitly by
    adding [with (m:=[c,d])] to the invocation of [apply]. *)

  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.   Qed.

(** Actually, we usually don't have to include the name [m] in
    the [with] clause; Coq is often smart enough to figure out which
    instantiation we're giving. We could instead write: [apply
    trans_eq with [c;d]]. *)

(** **** Exercise: 3 stars, standard, optional (apply_with_exercise)  *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with m.
  (* we basically say that we will prove the folliwing LHS = m = RHS *)
  apply eq2. apply eq1.
Qed.
(** [] *)

(* ################################################################# *)
(** * The [injection] and [discriminate] Tactics *)

(** Recall the definition of natural numbers:

     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.

    It is obvious from this definition that every number has one of
    two forms: either it is the constructor [O] or it is built by
    applying the constructor [S] to another number.  But there is more
    here than meets the eye: implicit in the definition (and in our
    informal understanding of how datatype declarations work in other
    programming languages) are two more facts:

    - The constructor [S] is _injective_.  That is, if [S n = S m], it
      must be the case that [n = m].

    - The constructors [O] and [S] are _disjoint_.  That is, [O] is not
      equal to [S n] for any [n].

    Similar principles apply to all inductively defined types: all
    constructors are injective, and the values built from distinct
    constructors are never equal.  For lists, the [cons] constructor
    is injective and [nil] is different from every non-empty list.
    For booleans, [true] and [false] are different.  (Since neither
    [true] nor [false] take any arguments, their injectivity is not
    interesting.)  And so on. *)

(** For example, we can prove the injectivity of [S] by using the
    [pred] function defined in [Basics.v]. *)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. } (* H2 is the name we give *)
  rewrite H2. rewrite H1. reflexivity.
Qed.

(** This technique can be generalized to any constructor by
    writing the equivalent of [pred] for that constructor -- i.e.,
    writing a function that "undoes" one application of the
    constructor. As a more convenient alternative, Coq provides a
    tactic called [injection] that allows us to exploit the
    injectivity of any constructor.  Here is an alternate proof of the
    above theorem using [injection]: *)

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.

(** By writing [injection H] at this point, we are asking Coq to
    generate all equations that it can infer from [H] using the
    injectivity of constructors. Each such equation is added as a
    premise to the goal. In the present example, adds the premise
    [n = m]. *)

  injection H. intros Hnm. apply Hnm.
Qed.

(** Here's a more interesting example that shows how [injection] can
    derive multiple equations at once. *)

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H. intros H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

(** The "[as]" variant of [injection] permits us to choose names for
    the introduced equations rather than letting Coq do it. *)

Theorem injection_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm. rewrite Hnm.
  reflexivity. Qed.

(** **** Exercise: 1 star, standard (injection_ex3)  *)
Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X.
  intros x y z l j eq1 eq2.
  injection eq1 as Ind1. (* this line is redundant *)
  injection eq2 as Ind2. (* the first elements of lists that are equal are equal *)
  symmetry. (* swap LHS and RHS of our claim *)
  rewrite Ind2.
  reflexivity.
Qed. 
(** [] *)

(** So much for injectivity of constructors.  What about disjointness?

    The principle of disjointness says that two terms beginning with
    different constructors (like [O] and [S], or [true] and [false])
    can never be equal.  This means that, any time we find ourselves
    working in a context where we've _assumed_ that two such terms are
    equal, we are justified in concluding anything we want to (because
    the assumption is nonsensical).

    The [discriminate] tactic embodies this principle: It is used on a
    hypothesis involving an equality between different
    constructors (e.g., [S n = O]), and it solves the current goal
    immediately.  For example: *)

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.

(** We can proceed by case analysis on [n]. The first case is
    trivial. *)

  destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.

(** However, the second one doesn't look so simple: assuming [0
    =? (S n') = true], we must show [S n' = 0]!  The way forward is to
    observe that the assumption itself is nonsensical: *)

  - (* n = S n' *)
    simpl.

(** If we use [discriminate] on this hypothesis, Coq confirms
    that the subgoal we are working on is impossible and removes it
    from further consideration. *)

    intros H. discriminate H.
Qed.

(** This is an instance of a logical principle known as the _principle
    of explosion_, which asserts that a contradictory hypothesis
    entails anything, even false things! *)

Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. discriminate contra. Qed.

(** If you find the principle of explosion confusing, remember
    that these proofs are _not_ showing that the conclusion of the
    statement holds.  Rather, they are showing that, if the
    nonsensical situation described by the premise did somehow arise,
    then the nonsensical conclusion would follow.  We'll explore the
    principle of explosion of more detail in the next chapter. *)

(** **** Exercise: 1 star, standard (discriminate_ex3)  *)
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X.
  intros x y z l j.
  intros contra.
  discriminate contra.
Qed.
  
(** [] *)

(** The injectivity of constructors allows us to reason that
    [forall (n m : nat), S n = S m -> n = m].  The converse of this
    implication is an instance of a more general fact about both
    constructors and functions, which we will find convenient in a few
    places below: *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.

(* ################################################################# *)
(** * Using Tactics on Hypotheses *)

(** By default, most tactics work on the goal formula and leave
    the context unchanged.  However, most tactics also have a variant
    that performs a similar operation on a statement in the context.

    For example, the tactic [simpl in H] performs simplification in
    the hypothesis named [H] in the context. *)

Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b  ->
     n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

(** Similarly, [apply L in H] matches some conditional statement
    [L] (of the form [X -> Y], say) against a hypothesis [H] in the
    context.  However, unlike ordinary [apply] (which rewrites a goal
    matching [Y] into a subgoal [X]), [apply L in H] matches [H]
    against [X] and, if successful, replaces it with [Y].

    In other words, [apply L in H] gives us a form of "forward
    reasoning": from [X -> Y] and a hypothesis matching [X], it
    produces a hypothesis matching [X].  By contrast, [apply L] is
    "backward reasoning": it says that if we know [X -> Y] and we
    are trying to prove [Y], it suffices to prove [X].

    Here is a variant of a proof from above, using forward reasoning
    throughout instead of backward reasoning. *)

Theorem silly3' : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5)  ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H.  Qed.

(** Forward reasoning starts from what is _given_ (premises,
    previously proven theorems) and iteratively draws conclusions from
    them until the goal is reached.  Backward reasoning starts from
    the _goal_, and iteratively reasons about what would imply the
    goal, until premises or previously proven theorems are reached.

    If you've seen informal proofs before (for example, in a math or
    computer science class), they probably used forward reasoning.  In
    general, idiomatic use of Coq tends to favor backward reasoning,
    but in some situations the forward style can be easier to think
    about.  *)

(** **** Exercise: 3 stars, standard, recommended (plus_n_n_injective)  

    Practice using "in" variants in this proof.  (Hint: use
    [plus_n_Sm].) *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  (* Check plus_n_Sm. *)
  (* The idea of the proof is to induct on n and check cases for m.
In fact, when we get to (0, 0) it is trivial and (0, S m') and (S n', 0)
we get contradiction. Thus, the only case we are left with is (S n', S m') *)

(* The 4th case is definitely much harder, but it actually doable
using injectivity twice and just manipulating with the conditions and
plus_n_Sm which is given as hint *) 
  intros n. induction n as [| n'].
  - destruct m as [|m']. (* check both cases for m *)
    + simpl. reflexivity. (* (0, 0) *)
    + intro contra. (* (0, S m') Should be contradiction. *)
      simpl in contra. discriminate contra.
 - destruct m as [|m'].
    + simpl. intros contra. discriminate contra.
    + simpl. intros H. injection H. intros H1.
      Check plus_n_Sm. 
      rewrite <- plus_n_Sm in H1. rewrite <- plus_n_Sm in H1. 
      injection H1. intros H2. apply IHn' in H2. apply f_equal. apply H2. 
Qed. 
(** [] *)

(* ################################################################# *)
(** * Varying the Induction Hypothesis *)

(** Sometimes it is important to control the exact form of the
    induction hypothesis when carrying out inductive proofs in Coq.
    In particular, we need to be careful about which of the
    assumptions we move (using [intros]) from the goal to the context
    before invoking the [induction] tactic.  For example, suppose
    we want to show that [double] is injective -- i.e., that it maps
    different arguments to different results:

       Theorem double_injective: forall n m,
         double n = double m -> n = m.

    The way we _start_ this proof is a bit delicate: if we begin with

       intros n. induction n.

    all is well.  But if we begin it with

       intros n m. induction n.

    we get stuck in the middle of the inductive case... *)



Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) apply f_equal.

(** At this point, the induction hypothesis, [IHn'], does _not_ give us
    [n' = m'] -- there is an extra [S] in the way -- so the goal is
    not provable. *)

      Abort.

(** What went wrong? *)

(** The problem is that, at the point we invoke the induction
    hypothesis, we have already introduced [m] into the context --
    intuitively, we have told Coq, "Let's consider some particular [n]
    and [m]..." and we now have to prove that, if [double n = double
    m] for _these particular_ [n] and [m], then [n = m].

    The next tactic, [induction n] says to Coq: We are going to show
    the goal by induction on [n].  That is, we are going to prove, for
    _all_ [n], that the proposition

      - [P n] = "if [double n = double m], then [n = m]"

    holds, by showing

      - [P O]

         (i.e., "if [double O = double m] then [O = m]") and

      - [P n -> P (S n)]

        (i.e., "if [double n = double m] then [n = m]" implies "if
        [double (S n) = double m] then [S n = m]").

    If we look closely at the second statement, it is saying something
    rather strange: it says that, for a _particular_ [m], if we know

      - "if [double n = double m] then [n = m]"

    then we can prove

       - "if [double (S n) = double m] then [S n = m]".

    To see why this is strange, let's think of a particular [m] --
    say, [5].  The statement is then saying that, if we know

      - [Q] = "if [double n = 10] then [n = 5]"

    then we can prove

      - [R] = "if [double (S n) = 10] then [S n = 5]".

    But knowing [Q] doesn't give us any help at all with proving
    [R]!  (If we tried to prove [R] from [Q], we would start with
    something like "Suppose [double (S n) = 10]..." but then we'd be
    stuck: knowing that [double (S n)] is [10] tells us nothing about
    whether [double n] is [10], so [Q] is useless.) *)

(** Trying to carry out this proof by induction on [n] when [m] is
    already in the context doesn't work because we are then trying to
    prove a statement involving _every_ [n] but just a _single_ [m]. *)

(** The successful proof of [double_injective] leaves [m] in the goal
    statement at the point where the [induction] tactic is invoked on
    [n]: *)

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.

  - (* n = S n' *) simpl.

(** Notice that both the goal and the induction hypothesis are
    different this time: the goal asks us to prove something more
    general (i.e., to prove the statement for _every_ [m]), but the IH
    is correspondingly more flexible, allowing us to choose any [m] we
    like when we apply the IH. *)

    intros m eq.

(** Now we've chosen a particular [m] and introduced the assumption
    that [double n = double m].  Since we are doing a case analysis on
    [n], we also need a case analysis on [m] to keep the two "in sync." *)

    destruct m as [| m'] eqn:E.
    + (* m = O *) simpl.

(** The 0 case is trivial: *)

      discriminate eq.

    + (* m = S m' *)
      apply f_equal.

(** At this point, since we are in the second branch of the [destruct
    m], the [m'] mentioned in the context is the predecessor of the
    [m] we started out talking about.  Since we are also in the [S]
    branch of the induction, this is perfect: if we instantiate the
    generic [m] in the IH with the current [m'] (this instantiation is
    performed automatically by the [apply] in the next step), then
    [IHn'] gives us exactly what we need to finish the proof. *)

      apply IHn'. injection eq as goal. apply goal. Qed.

(** What you should take away from all this is that we need to be
    careful, when using induction, that we are not trying to prove
    something too specific: To prove a property of [n] and [m] by
    induction on [n], it is sometimes important to leave [m]
    generic. *)

(** The following exercise requires the same pattern. *)

(** **** Exercise: 2 stars, standard (eqb_true)  *)
Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - intros m. destruct m.
    + simpl. reflexivity.
    + simpl. intros H. discriminate H.
  - intros m. destruct m.
    + simpl. intros H. discriminate H.
    + simpl. intros H. apply IHn' in H. apply f_equal. apply H.
Qed.

(** [] *)

(** **** Exercise: 2 stars, advanced (eqb_true_informal)  

    Give a careful informal proof of [eqb_true], being as explicit
    as possible about quantifiers. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_informal_proof : option (nat*string) := None.
(** [] *)

(** The strategy of doing fewer [intros] before an [induction] to
    obtain a more general IH doesn't always work by itself; sometimes
    some _rearrangement_ of quantified variables is needed.  Suppose,
    for example, that we wanted to prove [double_injective] by
    induction on [m] instead of [n]. *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
        (* Stuck again here, just like before. *)
Abort.

(** The problem is that, to do induction on [m], we must first
    introduce [n].  (If we simply say [induction m] without
    introducing anything first, Coq will automatically introduce [n]
    for us!)  *)

(** What can we do about this?  One possibility is to rewrite the
    statement of the lemma so that [m] is quantified before [n].  This
    works, but it's not nice: We don't want to have to twist the
    statements of lemmas to fit the needs of a particular strategy for
    proving them!  Rather we want to state them in the clearest and
    most natural way. *)

(** What we can do instead is to first introduce all the quantified
    variables and then _re-generalize_ one or more of them,
    selectively taking variables out of the context and putting them
    back at the beginning of the goal.  The [generalize dependent]
    tactic does this. *)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* [n] and [m] are both in the context *)
  generalize dependent n.
  (* Now [n] is back in the goal and we can do induction on
     [m] and get a sufficiently general IH. *)
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.

(** Let's look at an informal proof of this theorem.  Note that
    the proposition we prove by induction leaves [n] quantified,
    corresponding to the use of generalize dependent in our formal
    proof.

    _Theorem_: For any nats [n] and [m], if [double n = double m], then
      [n = m].

    _Proof_: Let [m] be a [nat]. We prove by induction on [m] that, for
      any [n], if [double n = double m] then [n = m].

      - First, suppose [m = 0], and suppose [n] is a number such
        that [double n = double m].  We must show that [n = 0].

        Since [m = 0], by the definition of [double] we have [double n =
        0].  There are two cases to consider for [n].  If [n = 0] we are
        done, since [m = 0 = n], as required.  Otherwise, if [n = S n']
        for some [n'], we derive a contradiction: by the definition of
        [double], we can calculate [double n = S (S (double n'))], but
        this contradicts the assumption that [double n = 0].

      - Second, suppose [m = S m'] and that [n] is again a number such
        that [double n = double m].  We must show that [n = S m'], with
        the induction hypothesis that for every number [s], if [double s =
        double m'] then [s = m'].

        By the fact that [m = S m'] and the definition of [double], we
        have [double n = S (S (double m'))].  There are two cases to
        consider for [n].

        If [n = 0], then by definition [double n = 0], a contradiction.

        Thus, we may assume that [n = S n'] for some [n'], and again by
        the definition of [double] we have [S (S (double n')) =
        S (S (double m'))], which implies by injectivity that [double n' =
        double m'].  Instantiating the induction hypothesis with [n'] thus
        allows us to conclude that [n' = m'], and it follows immediately
        that [S n' = S m'].  Since [S n' = n] and [S m' = m], this is just
        what we wanted to show. [] *)

(** Before we close this section and move on to some exercises,
    let's digress briefly and use [eqb_true] to prove a similar
    property of identifiers that we'll need in later chapters: *)

Search eqb.

Theorem eqb_id_true : forall x y,
  eqb_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). {apply eqb_true. apply H. }
  rewrite H'. reflexivity.
Qed.

(** **** Exercise: 3 stars, standard, recommended (gen_dep_practice)  

    Prove this by induction on [l]. *)

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  Check nth_error.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Unfolding Definitions *)

(** It sometimes happens that we need to manually unfold a name that
    has been introduced by a [Definition] so that we can manipulate
    its right-hand side.  For example, if we define... *)

Definition square n := n * n.

(** ... and try to prove a simple fact about [square]... *)

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.

(** ... we appear to be stuck: [simpl] doesn't simplify anything at
    this point, and since we haven't proved any other facts about
    [square], there is nothing we can [apply] or [rewrite] with.

    To make progress, we can manually [unfold] the definition of
    [square]: *)

  unfold square.

(** Now we have plenty to work with: both sides of the equality are
    expressions involving multiplication, and we have lots of facts
    about multiplication at our disposal.  In particular, we know that
    it is commutative and associative, and from these it is not hard
    to finish the proof. *)

  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

(** At this point, some discussion of unfolding and simplification is
    in order.

    You may already have observed that tactics like [simpl],
    [reflexivity], and [apply] will often unfold the definitions of
    functions automatically when this allows them to make progress.
    For example, if we define [foo m] to be the constant [5]... *)

Definition foo (x: nat) := 5.

(** .... then the [simpl] in the following proof (or the
    [reflexivity], if we omit the [simpl]) will unfold [foo m] to
    [(fun x => 5) m] and then further simplify this expression to just
    [5]. *)

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

(** However, this automatic unfolding is somewhat conservative.  For
    example, if we define a slightly more complicated function
    involving a pattern match... *)

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

(** ...then the analogous proof will get stuck: *)

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

(** The reason that [simpl] doesn't make progress here is that it
    notices that, after tentatively unfolding [bar m], it is left with
    a match whose scrutinee, [m], is a variable, so the [match] cannot
    be simplified further.  It is not smart enough to notice that the
    two branches of the [match] are identical, so it gives up on
    unfolding [bar m] and leaves it alone.  Similarly, tentatively
    unfolding [bar (m+1)] leaves a [match] whose scrutinee is a
    function application (that cannot itself be simplified, even
    after unfolding the definition of [+]), so [simpl] leaves it
    alone. *)

(** At this point, there are two ways to make progress.  One is to use
    [destruct m] to break the proof into two cases, each focusing on a
    more concrete choice of [m] ([O] vs [S _]).  In each case, the
    [match] inside of [bar] can now make progress, and the proof is
    easy to complete. *)

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** This approach works, but it depends on our recognizing that the
    [match] hidden inside [bar] is what was preventing us from making
    progress. *)

(** A more straightforward way to make progress is to explicitly tell
    Coq to unfold [bar]. *)

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.

(** Now it is apparent that we are stuck on the [match] expressions on
    both sides of the [=], and we can use [destruct] to finish the
    proof without thinking too hard. *)

  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

(* ################################################################# *)
(** * Using [destruct] on Compound Expressions *)

(** We have seen many examples where [destruct] is used to
    perform case analysis of the value of some variable.  But
    sometimes we need to reason by cases on the result of some
    _expression_.  We can also do this with [destruct].

    Here are some examples: *)

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity.  Qed.

(** After unfolding [sillyfun] in the above proof, we find that
    we are stuck on [if (n =? 3) then ... else ...].  But either
    [n] is equal to [3] or it isn't, so we can use [destruct (eqb
    n 3)] to let us reason about the two cases.

    In general, the [destruct] tactic can be used to perform case
    analysis of the results of arbitrary computations.  If [e] is an
    expression whose type is some inductively defined type [T], then,
    for each constructor [c] of [T], [destruct e] generates a subgoal
    in which all occurrences of [e] (in the goal and in the context)
    are replaced by [c]. *)

(** **** Exercise: 3 stars, standard, optional (combine_split)  

    Here is an implementation of the [split] function mentioned in
    chapter [Poly]: *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

(** Prove that [split] and [combine] are inverses in the following
    sense: *)


(* split [(1,false);(2,false)] = ([1;2],[false;false]). *)

(* combine [1;2] [false;false;true;true]) = [(1, false); (2, false)]
     : list (nat * bool)
*) 

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
(* FILL IN HERE *)
  intros X Y l.
  induction l as [| h t IH]. (*if l is [], it must be that l1=l2=[] *)
  -simpl. intros l1 l2. intros H.
  injection H. intros H2. intros H1.  (* that follows directly *)
  symmetry. rewrite <- H1. rewrite <- H2. simpl. reflexivity.
  -intros l1 l2. intros H. (*h is a pair, t is a list of pairs *)
  destruct t.
    + inversion H.
Admitted.
 (* apply IH in H.


Qed.
*)

(** [] *)

(** The [eqn:] part of the [destruct] tactic is optional: We've chosen
    to include it most of the time, just for the sake of
    documentation, but many Coq proofs omit it.

    When [destruct]ing compound expressions, however, the information
    recorded by the [eqn:] can actually be critical: if we leave it
    out, then [destruct] can sometimes erase information we need to
    complete a proof. 

    For example, suppose we define a function [sillyfun1] like
    this: *)

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

(** Now suppose that we want to convince Coq of the (rather
    obvious) fact that [sillyfun1 n] yields [true] only when [n] is
    odd.  If we start the proof like this (with no [eqn:] on the
    destruct)... *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* stuck... *)
Abort.

(** ... then we are stuck at this point because the context does
    not contain enough information to prove the goal!  The problem is
    that the substitution performed by [destruct] is quite brutal --
    in this case, it thows away every occurrence of [n =? 3], but we
    need to keep some memory of this expression and how it was
    destructed, because we need to be able to reason that, since [n =?
    3 = true] in this branch of the case analysis, it must be that [n
    = 3], from which it follows that [n] is odd.

    What we want here is to substitute away all existing occurences of
    [n =? 3], but at the same time add an equation to the context that
    records which case we are in.  This is precisely what the [eqn:]
    qualifier does. *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got
     stuck above, except that the context contains an extra
     equality assumption, which is exactly what we need to
     make progress. *)
    - (* e3 = true *) apply eqb_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
     (* When we come to the second equality test in the body
        of the function we are reasoning about, we can use
        [eqn:] again in the same way, allowing us to finish the
        proof. *)
      destruct (n =? 5) eqn:Heqe5.
        + (* e5 = true *)
          apply eqb_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) discriminate eq.  Qed.

(** **** Exercise: 2 stars, standard (destruct_eqn_practice)  *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  (* This problem can easily be brute-forced by checking all cases for 
b and f(b). *)
  intros f b. 
  destruct b. (* two cases for b *)
  -destruct (f true) eqn:f_o_t. (* two cases for (f true) *)
    + rewrite f_o_t. rewrite f_o_t. reflexivity. (* f_o_t stands for f(true) *) 
    + destruct (f false) eqn:f_o_f. (* two cases for (f false) *)
      * apply f_o_t.
      * apply f_o_f.
  -destruct (f false) eqn:f_o_f.
    + destruct (f true) eqn:f_o_t.
      * apply f_o_t.
      * apply f_o_f.
    + rewrite f_o_f. apply f_o_f.
Qed.

(** [] *)

(* ################################################################# *)
(** * Review *)

(** We've now seen many of Coq's most fundamental tactics.  We'll
    introduce a few more in the coming chapters, and later on we'll
    see some more powerful _automation_ tactics that make Coq help us
    with low-level details.  But basically we've got what we need to
    get work done.

    Here are the ones we've seen:

      - [intros]: move hypotheses/variables from goal to context

      - [reflexivity]: finish the proof (when the goal looks like [e =
        e])

      - [apply]: prove goal using a hypothesis, lemma, or constructor

      - [apply... in H]: apply a hypothesis, lemma, or constructor to
        a hypothesis in the context (forward reasoning)

      - [apply... with...]: explicitly specify values for variables
        that cannot be determined by pattern matching

      - [simpl]: simplify computations in the goal

      - [simpl in H]: ... or a hypothesis

      - [rewrite]: use an equality hypothesis (or lemma) to rewrite
        the goal

      - [rewrite ... in H]: ... or a hypothesis

      - [symmetry]: changes a goal of the form [t=u] into [u=t]

      - [symmetry in H]: changes a hypothesis of the form [t=u] into
        [u=t]

      - [unfold]: replace a defined constant by its right-hand side in
        the goal

      - [unfold... in H]: ... or a hypothesis

      - [destruct... as...]: case analysis on values of inductively
        defined types

      - [destruct... eqn:...]: specify the name of an equation to be
        added to the context, recording the result of the case
        analysis

      - [induction... as...]: induction on values of inductively
        defined types

      - [injection]: reason by injectivity on equalities
        between values of inductively defined types

      - [discriminate]: reason by disjointness of constructors on
        equalities between values of inductively defined types

      - [assert (H: e)] (or [assert (e) as H]): introduce a "local
        lemma" [e] and call it [H]

      - [generalize dependent x]: move the variable [x] (and anything
        else that depends on it) from the context back to an explicit
        hypothesis in the goal formula *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard (eqb_sym)  *)
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (eqb_sym_informal)  

    Give an informal proof of this lemma that corresponds to your
    formal proof above:

   Theorem: For any [nat]s [n] [m], [(n =? m) = (m =? n)].

   Proof: *)
   (* FILL IN HERE 

    [] *)

(** **** Exercise: 3 stars, standard, optional (eqb_trans)  *)
Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (split_combine)  

    We proved, in an exercise above, that for all lists of pairs,
    [combine] is the inverse of [split].  How would you formalize the
    statement that [split] is the inverse of [combine]?  When is this
    property true?

    Complete the definition of [split_combine_statement] below with a
    property that states that [split] is the inverse of
    [combine]. Then, prove that the property holds. (Be sure to leave
    your induction hypothesis general by not doing [intros] on more
    things than necessary.  Hint: what property do you need of [l1]
    and [l2] for [split (combine l1 l2) = (l1,l2)] to be true?) *)

Definition split_combine_statement : Prop
  (* ("[: Prop]" means that we are giving a name to a
     logical proposition here.) *) := forall X Y (l1 : list X) (l2 : list Y) l, 
combine l1 l2 = l -> split l = (l1, l2). 

(* split [(1,false);(2,false)] = ([1;2],[false;false]). *)

(* combine [1;2] [false;false;true;true]) = [(1, false); (2, false)]
     : list (nat * bool)
*) 

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l1 l2. 
  induction l1 as[|h1 t1].
  -destruct l2 as[|h2 t2].
    +simpl. intros. rewrite <- H. simpl. reflexivity.
    +intros l. intros H. inversion H. simpl.

(* FILL IN HERE *) Admitted.

(* Do not modify the following line: *)
Definition manual_grade_for_split_combine : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, advanced (filter_exercise)  

    This one is a bit challenging.  Pay attention to the form of your
    induction hypothesis. *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, recommended (forall_exists_challenge)  

    Define two recursive [Fixpoints], [forallb] and [existsb].  The
    first checks whether every element in a list satisfies a given
    predicate:

      forallb oddb [1;3;5;7;9] = true

      forallb negb [false;false] = true

      forallb evenb [0;2;4;5] = false

      forallb (eqb 5) [] = true

    The second checks whether there exists an element in the list that
    satisfies a given predicate:

      existsb (eqb 5) [0;2;3;6] = false

      existsb (andb true) [true;true;false] = true

      existsb oddb [1;0;0;0;0;3] = true

      existsb evenb [] = false

    Next, define a _nonrecursive_ version of [existsb] -- call it
    [existsb'] -- using [forallb] and [negb].

    Finally, prove a theorem [existsb_existsb'] stating that
    [existsb'] and [existsb] have the same behavior. *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. (* FILL IN HERE *) Admitted.

Example test_forallb_2 : forallb negb [false;false] = true.
Proof. (* FILL IN HERE *) Admitted.

Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. (* FILL IN HERE *) Admitted.

Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. (* FILL IN HERE *) Admitted.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. (* FILL IN HERE *) Admitted.

Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. (* FILL IN HERE *) Admitted.

Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. (* FILL IN HERE *) Admitted.

Example test_existsb_4 : existsb evenb [] = false.
Proof. (* FILL IN HERE *) Admitted.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)



(* Wed Jan 9 12:02:44 EST 2019 *)










(** * Logic: Logic in Coq *)

Set Warnings "-notation-overridden,-parsing".

(** In previous chapters, we have seen many examples of factual
    claims (_propositions_) and ways of presenting evidence of their
    truth (_proofs_).  In particular, we have worked extensively with
    _equality propositions_ of the form [e1 = e2], with
    implications ([P -> Q]), and with quantified propositions ([forall
    x, P]).  In this chapter, we will see how Coq can be used to carry
    out other familiar forms of logical reasoning.

    Before diving into details, let's talk a bit about the status of
    mathematical statements in Coq.  Recall that Coq is a _typed_
    language, which means that every sensible expression in its world
    has an associated type.  Logical claims are no exception: any
    statement we might try to prove in Coq has a type, namely [Prop],
    the type of _propositions_.  We can see this with the [Check]
    command: *)

Check 3 = 3.
(* ===> Prop *)

Check forall n m : nat, n + m = m + n.
(* ===> Prop *)

(** Note that _all_ syntactically well-formed propositions have type
    [Prop] in Coq, regardless of whether they are true. *)

(** Simply _being_ a proposition is one thing; being _provable_ is
    something else! *)

Check 2 = 2.
(* ===> Prop *)

Check forall n : nat, n = 2.
(* ===> Prop *)

Check 3 = 4.
(* ===> Prop *)

(** Indeed, propositions don't just have types: they are
    _first-class objects_ that can be manipulated in the same ways as
    the other entities in Coq's world. *)

(** So far, we've seen one primary place that propositions can appear:
    in [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But propositions can be used in many other ways.  For example, we
    can give a name to a proposition using a [Definition], just as we
    have given names to expressions of other sorts. *)

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity.  Qed.

(** We can also write _parameterized_ propositions -- that is,
    functions that take arguments of some type and return a
    proposition. *)

(** For instance, the following function takes a number
    and returns a proposition asserting that this number is equal to
    three: *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* ===> nat -> Prop *)

(** In Coq, functions that return propositions are said to define
    _properties_ of their arguments.

    For instance, here's a (polymorphic) property defining the
    familiar notion of an _injective function_. *)

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. injection H as H1. apply H1.
Qed.

(** The equality operator [=] is also a function that returns a
    [Prop].

    The expression [n = m] is syntactic sugar for [eq n m] (defined
    using Coq's [Notation] mechanism). Because [eq] can be used with
    elements of any type, it is also polymorphic: *)

Check @eq.
(* ===> forall A : Type, A -> A -> Prop *)

(** (Notice that we wrote [@eq] instead of [eq]: The type
    argument [A] to [eq] is declared as implicit, so we need to turn
    off implicit arguments to see the full type of [eq].) *)

(* ################################################################# *)
(** * Logical Connectives *)

(* ================================================================= *)
(** ** Conjunction *)

(** The _conjunction_, or _logical and_, of propositions [A] and [B]
    is written [A /\ B], representing the claim that both [A] and [B]
    are true. *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(** To prove a conjunction, use the [split] tactic.  It will generate
    two subgoals, one for each part of the statement: *)

Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** For any propositions [A] and [B], if we assume that [A] is true
    and we assume that [B] is true, we can conclude that [A /\ B] is
    also true. *)

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

(** Since applying a theorem with hypotheses to some goal has the
    effect of generating as many subgoals as there are hypotheses for
    that theorem, we can apply [and_intro] to achieve the same effect
    as [split]. *)

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (and_exercise)  *)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m.
  intros H.
  apply and_intro.
  - induction n as [| n' IHn'].
    + reflexivity.
    + discriminate.
  - induction m as [| m' IHn'].
    + reflexivity.
    + rewrite plus_comm in H. discriminate.
Qed. 

(** [] *)

(** So much for proving conjunctive statements.  To go in the other
    direction -- i.e., to _use_ a conjunctive hypothesis to help prove
    something else -- we employ the [destruct] tactic.

    If the proof context contains a hypothesis [H] of the form
    [A /\ B], writing [destruct H as [HA HB]] will remove [H] from the
    context and add two new hypotheses: [HA], stating that [A] is
    true, and [HB], stating that [B] is true.  *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** As usual, we can also destruct [H] right when we introduce it,
    instead of introducing and then destructing it: *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** You may wonder why we bothered packing the two hypotheses [n = 0]
    and [m = 0] into a single conjunction, since we could have also
    stated the theorem with two separate premises: *)

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** For this theorem, both formulations are fine.  But it's important
    to understand how to work with conjunctive hypotheses because
    conjunctions often arise from intermediate steps in proofs,
    especially in bigger developments.  Here's a simple example: *)

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

(** Another common situation with conjunctions is that we know
    [A /\ B] but in some context we need just [A] (or just [B]).
    The following lemmas are useful in such cases: *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.  Qed.

(** **** Exercise: 1 star, standard, optional (proj2)  *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  apply HQ.
Qed.
(** [] *)

(** Finally, we sometimes need to rearrange the order of conjunctions
    and/or the grouping of multi-way conjunctions.  The following
    commutativity and associativity theorems are handy in such
    cases. *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.  Qed.

(** **** Exercise: 2 stars, standard (and_assoc)  

    (In the following proof of associativity, notice how the _nested_
    [intros] pattern breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP : P], [HQ : Q], and [HR : R].  Finish the proof from
    there.) *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  -apply and_intro. apply HP. apply HQ.
  -apply HR.
Qed.
(** [] *)

(** By the way, the infix notation [/\] is actually just syntactic
    sugar for [and A B].  That is, [and] is a Coq operator that takes
    two propositions as arguments and yields a proposition. *)

Check and.
(* ===> and : Prop -> Prop -> Prop *)

(* ================================================================= *)
(** ** Disjunction *)

(** Another important connective is the _disjunction_, or _logical or_,
    of two propositions: [A \/ B] is true when either [A] or [B]
    is.  (This infix notation stands for [or A B], where [or : Prop ->
    Prop -> Prop].) *)

(** To use a disjunctive hypothesis in a proof, we proceed by case
    analysis, which, as for [nat] or other data types, can be done
    explicitly with [destruct] or implicitly with an [intros] pattern: *)

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     [n = 0 \/ m = 0] *)
  intros n m [Hn | Hm].
  - (* Here, [n = 0] *)
    rewrite Hn. reflexivity.
  - (* Here, [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(** Conversely, to show that a disjunction holds, we need to show that
    one of its sides does. This is done via two tactics, [left] and
    [right].  As their names imply, the first one requires
    proving the left side of the disjunction, while the second
    requires proving its right side.  Here is a trivial use... *)

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

(** ... and here is a slightly more interesting example requiring both
    [left] and [right]: *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  (* intros n. 
  destruct n. *)
  intros [|n]. (* equivalent to the previous line *)
  - left. reflexivity.
  - right. simpl. reflexivity.
Qed.

(** **** Exercise: 1 star, standard (mult_eq_0)  *)
Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros [|n].
  -left. reflexivity.
  - intros [|m].
    + right. reflexivity.
    + intros H.  discriminate H. (*it can't be the case that S n * S m = 0 *)

Qed.
(** **** Exercise: 1 star, standard (or_commut)  *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q [HP|HQ]. 
(*again, [HP|HQ] just creates two cases, one where each is true *)
  -right. apply HP.
  -left. apply HQ.
Qed.
  
(* ================================================================= *)
(** ** Falsehood and Negation 

    So far, we have mostly been concerned with proving that certain
    things are _true_ -- addition is commutative, appending lists is
    associative, etc.  Of course, we may also be interested in
    negative results, showing that some given proposition is _not_
    true. In Coq, such statements are expressed with the negation
    operator [~]. *)

(** To see how negation works, recall the _principle of explosion_
    from the [Tactics] chapter; it asserts that, if we assume a
    contradiction, then any other proposition can be derived.

    Following this intuition, we could define [~ P] ("not [P]") as
    [forall Q, P -> Q].

    Coq actually makes a slightly different (but equivalent) choice,
    defining [~ P] as [P -> False], where [False] is a specific
    contradictory proposition defined in the standard library. *)

Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

End MyNot.

(** Since [False] is a contradictory proposition, the principle of
    explosion also applies to it. If we get [False] into the proof
    context, we can use [destruct] on it to complete any goal: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra.  Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from falsehood
    follows whatever you like"; this is another common name for the
    principle of explosion. *)

(** **** Exercise: 2 stars, standard, optional (not_implies_our_not)  

    Show that Coq's definition of negation implies the intuitive one
    mentioned above: *)

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P notP.
  intros Q.
  intros H.
  apply notP in H. (* it's not possible that P and notP are both true *)
  destruct H. (* we have a false premise, thus any result is true *)
Qed.

(** Inequality is a frequent enough example of negated statement
    that there is a special notation for it, [x <> y]:

      Notation "x <> y" := (~(x = y)).
*)

(** We can use [not] to state that [0] and [1] are different elements
    of [nat]: *)

Theorem zero_not_one : 0 <> 1.
Proof.
  (** The proposition [0 <> 1] is exactly the same as
      [~(0 = 1)], that is [not (0 = 1)], which unfolds to
      [(0 = 1) -> False]. (We use [unfold not] explicitly here
      to illustrate that point, but generally it can be omitted.) *)
  unfold not.
  (** To prove an inequality, we may assume the opposite
      equality... *)
  intros contra.
  (** ... and deduce a contradiction from it. Here, the
      equality [O = S O] contradicts the disjointness of
      constructors [O] and [S], so [discriminate] takes care
      of it. *)
  discriminate contra.
Qed.

(** It takes a little practice to get used to working with negation in
    Coq.  Even though you can see perfectly well why a statement
    involving negation is true, it can be a little tricky at first to
    get things into the right configuration so that Coq can understand
    it!  Here are proofs of a few familiar facts to get you warmed
    up. *)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H.
  unfold not.
  intros G.
  apply G.
  apply H.
Qed.

(** **** Exercise: 2 stars, advanced (double_neg_inf)  

    Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P]. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_double_neg_inf : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, recommended (contrapositive)  *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q.
  intros H1. (* the condition, i.e. (P->Q) *)
  unfold not. (* simple unfold followed by the two hypothesis we can deduce *) 
  intros H2.  
  intros H3.
  apply H2. (* just applying the three hypothesis in the needed order *)
  apply H1.
  apply H3.
Qed.

(** [] *)

(** **** Exercise: 1 star, standard (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P.
  unfold not. (* the classical trick *)
  intros [H1 H2]. (* introduce the two parts of the and *)
  apply H2. (* just apply them properly to end the proof *)
  apply H1.
Qed.

(** [] *)

(** **** Exercise: 1 star, advanced (informal_not_PNP)  

    Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_informal_not_PNP : option (nat*string) := None.
(** [] *)

(** Similarly, since inequality involves a negation, it requires a
    little practice to be able to work with it fluently.  Here is one
    useful trick.  If you are trying to prove a goal that is
    nonsensical (e.g., the goal state is [false = true]), apply
    [ex_falso_quodlibet] to change the goal to [False].  This makes it
    easier to use assumptions of the form [~P] that may be available
    in the context -- in particular, assumptions of the form
    [x<>y]. *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  (* intros b H.
  destruct b. ---- these two lines are the same as the next one*)
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(** Since reasoning with [ex_falso_quodlibet] is quite common, Coq
    provides a built-in tactic, [exfalso], for applying it. *)

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    exfalso.                (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

(* ================================================================= *)
(** ** Truth *)

(** Besides [False], Coq's standard library also defines [True], a
    proposition that is trivially true. To prove it, we use the
    predefined constant [I : True]: *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(** Unlike [False], which is used extensively, [True] is used quite
    rarely, since it is trivial (and therefore uninteresting) to prove
    as a goal, and it carries no useful information as a hypothesis. 

    But it can be quite useful when defining complex [Prop]s using
    conditionals or as a parameter to higher-order [Prop]s.
    We will see examples of such uses of [True] later on. *)

(* ================================================================= *)
(** ** Logical Equivalence *)

(** The handy "if and only if" connective, which asserts that two
    propositions have the same truth value, is just the conjunction of
    two implications. *)

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA]. (*H is <->. We just take both separately *)
  split. (* the things we want to prove *)
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.  Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split. (* we'll prove both directions separately *)
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

(** **** Exercise: 1 star, standard, optional (iff_properties)  

    Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split.
  -intros H. apply H.
  -intros H. apply H.
  
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R.
  intros [PQ QP].
  intros [QR RQ].
  split.
  -intros HP. apply QR. apply PQ. apply HP.
  -intros HR. apply QP. apply RQ. apply HR.

Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - (* -> *)
    intros [HP | [HQ HR]].
    + split. 
      * left. apply HP. (*or_intro: A → A ∨ B. *) 
      * left. apply HP.
    + split.
      * right. apply HQ.
      * right. apply HR.

  - (* <- *)
    intros [[HP | HQ] [HP' | HR]].
    + left. apply HP.
    + left. apply HP.
    + left. apply HP'.
    + right. split.
      * apply HQ.
      * apply HR.
Qed.

(** [] *)

(** Some of Coq's tactics treat [iff] statements specially, avoiding
    the need for some low-level proof-state manipulation.  In
    particular, [rewrite] and [reflexivity] can be used with [iff]
    statements, not just equalities.  To enable this behavior, we need
    to import a Coq library that supports it: *)

From Coq Require Import Setoids.Setoid.

(** Here is a simple example demonstrating how these tactics work with
    [iff].  First, let's prove a couple of basic iff equivalences... *)

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [HP | [HQ | HR]]. (* could have only been with H as in the next bulletpoint *)
    + left. left. apply HP.
    + left. right. apply HQ.
    + right. apply HR.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(** We can now use these facts with [rewrite] and [reflexivity] to
    give smooth proofs of statements involving equivalences.  Here is
    a ternary version of the previous [mult_0] result: *)

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

(** The [apply] tactic can also be used with [<->]. When given an
    equivalence as its argument, [apply] tries to guess which side of
    the equivalence to use. *)

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

(* ================================================================= *)
(** ** Existential Quantification *)

(** Another important logical connective is _existential
    quantification_.  To say that there is some [x] of type [T] such
    that some property [P] holds of [x], we write [exists x : T,
    P]. As with [forall], the type annotation [: T] can be omitted if
    Coq is able to infer from the context what the type of [x] should
    be. *)

(** To prove a statement of the form [exists x, P], we must show that
    [P] holds for some specific choice of value for [x], known as the
    _witness_ of the existential.  This is done in two steps: First,
    we explicitly tell Coq which witness [t] we have in mind by
    invoking the tactic [exists t].  Then we prove that [P] holds after
    all occurrences of [x] are replaced by [t]. *)

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note implicit [destruct] here *)
  exists (2 + m).
  apply Hm.  Qed.

(** **** Exercise: 1 star, standard, recommended (dist_not_exists)  

    Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold."  (Hint: [destruct H as [x E]] works on
    existential assumptions!)  *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros P p. (* the type and a proposition *)
  intros H_all. (* universal quantification *) 
  unfold not. (* we want to prove STH -> False. *)
  intros [witness H_exist]. (* existential quantification and the witness (variable) *)
  apply H_exist.
  apply H_all. (* end the proof *)
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (dist_exists_or)  

    Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - (* -> *)
    intros [witness [HP | HQ]]. (* either P x is true, or Q x *)
    + left. exists witness. apply HP. (* we just use the witness from earlier *) 
    + right. exists witness. apply HQ.
  - (* <- *)
    intros [[witness HP] | [witness HQ]]. (*we either have a witness for P x, or for Q x *)
    + exists witness. left. apply HP. (* use the witness and finish *)
    + exists witness. right. apply HQ.
Qed.

(** [] *)

(* ################################################################# *)
(** * Programming with Propositions *)

(** The logical connectives that we have seen provide a rich
    vocabulary for defining complex propositions from simpler ones.
    To illustrate, let's look at how to express the claim that an
    element [x] occurs in a list [l].  Notice that this property has a
    simple recursive structure: 

       - If [l] is the empty list, then [x] cannot occur on it, so the
         property "[x] appears in [l]" is simply false. 

       - Otherwise, [l] has the form [x' :: l'].  In this case, [x]
         occurs in [l] if either it is equal to [x'] or it occurs in
         [l']. *)

(** We can translate this directly into a straightforward recursive
    function taking an element and a list and returning a proposition: *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested disjunctions. *)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.
(** (Notice the use of the empty pattern to discharge the last case
    _en passant_.) *)

(** We can also prove more generic, higher-level lemmas about [In].

    Note, in the next, how [In] starts out applied to a variable and
    only gets expanded when we do case analysis on this variable: *)

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(** This way of defining propositions recursively, though convenient
    in some cases, also has some drawbacks.  In particular, it is
    subject to Coq's usual restrictions regarding the definition of
    recursive functions, e.g., the requirement that they be "obviously
    terminating."  In the next chapter, we will see how to define
    propositions _inductively_, a different technique with its own set
    of strengths and limitations. *)

(** **** Exercise: 2 stars, standard (In_map_iff)  *)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (In_app_iff)  *)
Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, recommended (All)  

    Recall that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] states that property [P] holds of [n].

    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (combine_odd_even)  

    Complete the definition of the [combine_odd_even] function below.
    It takes as arguments two properties of numbers, [Podd] and
    [Peven], and it should return a property [P] such that [P n] is
    equivalent to [Podd n] when [n] is odd and equivalent to [Peven n]
    otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** To test your definition, prove the following facts: *)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Applying Theorems to Arguments *)

(** One feature of Coq that distinguishes it from some other
    popular proof assistants (e.g., ACL2 and Isabelle) is that it
    treats _proofs_ as first-class objects.

    There is a great deal to be said about this, but it is not
    necessary to understand it all in detail in order to use Coq.  This
    section gives just a taste, while a deeper exploration can be
    found in the optional chapters [ProofObjects] and
    [IndPrinciples]. *)

(** We have seen that we can use the [Check] command to ask Coq to
    print the type of an expression.  We can also use [Check] to ask
    what theorem a particular identifier refers to. *)

Check plus_comm.
(* ===> forall n m : nat, n + m = m + n *)

(** Coq prints the _statement_ of the [plus_comm] theorem in the same
    way that it prints the _type_ of any term that we ask it to
    [Check].  Why? *)

(** The reason is that the identifier [plus_comm] actually refers to a
    _proof object_ -- a data structure that represents a logical
    derivation establishing of the truth of the statement [forall n m
    : nat, n + m = m + n].  The type of this object _is_ the statement
    of the theorem that it is a proof of. *)

(** Intuitively, this makes sense because the statement of a theorem
    tells us what we can use that theorem for, just as the type of a
    computational object tells us what we can do with that object --
    e.g., if we have a term of type [nat -> nat -> nat], we can give
    it two [nat]s as arguments and get a [nat] back.  Similarly, if we
    have an object of type [n = m -> n + n = m + m] and we provide it
    an "argument" of type [n = m], we can derive [n + n = m + m]. *)

(** Operationally, this analogy goes even further: by applying a
    theorem, as if it were a function, to hypotheses with matching
    types, we can specialize its result without having to resort to
    intermediate assertions.  For example, suppose we wanted to prove
    the following result: *)

Lemma plus_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.

(** It appears at first sight that we ought to be able to prove this
    by rewriting with [plus_comm] twice to make the two sides match.
    The problem, however, is that the second [rewrite] will undo the
    effect of the first. *)

Proof.
  (* WORKED IN CLASS *)
  intros x y z.
  rewrite plus_comm.
  rewrite plus_comm.
  (* We are back where we started... *)
Abort.

(** One simple way of fixing this problem, using only tools that we
    already know, is to use [assert] to derive a specialized version
    of [plus_comm] that can be used to rewrite exactly where we
    want. *)

Lemma plus_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

(** A more elegant alternative is to apply [plus_comm] directly to the
    arguments we want to instantiate it with, in much the same way as
    we apply a polymorphic function to a type argument. *)

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

(** Let us show another example of using a theorem or lemma
    like a function. The following theorem says: any list [l]
    containing some element must be nonempty. *)

Lemma in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl. destruct l.
  - simpl in H. destruct H.
  - discriminate Hl.
Qed.

(** What makes this interesting is that one quantified variable
    ([x]) does not appear in the conclusion ([l <> []]). *)

(** We can use this lemma to prove the special case where [x]
    is [42]. Naively, the tactic [apply in_not_nil] will fail because
    it cannot infer the value of [x]. There are several ways to work
    around that... *)

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  (* WORKED IN CLASS *)
  intros l H.
  Fail apply in_not_nil.
Abort.

(* [apply ... with ...] *)
Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(* [apply ... in ...] *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(* Explicitly apply the lemma to the value for [x]. *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(* Explicitly apply the lemma to a hypothesis. *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

(** You can "use theorems as functions" in this way with almost all
    tactics that take a theorem name as an argument.  Note also that
    theorem application uses the same inference mechanisms as function
    application; thus, it is possible, for example, to supply
    wildcards as arguments to be inferred, or to declare some
    hypotheses to a theorem as implicit by default.  These features
    are illustrated in the proof below. (The details of how this proof
    works are not critical -- the goal here is just to illustrate what
    can be done.) *)

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(** We will see many more examples in later chapters. *)

(* ################################################################# *)
(** * Coq vs. Set Theory *)

(** Coq's logical core, the _Calculus of Inductive
    Constructions_, differs in some important ways from other formal
    systems that are used by mathematicians to write down precise and
    rigorous proofs.  For example, in the most popular foundation for
    paper-and-pencil mathematics, Zermelo-Fraenkel Set Theory (ZFC), a
    mathematical object can potentially be a member of many different
    sets; a term in Coq's logic, on the other hand, is a member of at
    most one type.  This difference often leads to slightly different
    ways of capturing informal mathematical concepts, but these are,
    by and large, about equally natural and easy to work with.  For
    example, instead of saying that a natural number [n] belongs to
    the set of even numbers, we would say in Coq that [even n] holds,
    where [even : nat -> Prop] is a property describing even numbers.

    However, there are some cases where translating standard
    mathematical reasoning into Coq can be cumbersome or sometimes
    even impossible, unless we enrich the core logic with additional
    axioms.

    We conclude this chapter with a brief discussion of some of the
    most significant differences between the two worlds. *)

(* ================================================================= *)
(** ** Functional Extensionality *)

(** The equality assertions that we have seen so far mostly have
    concerned elements of inductive types ([nat], [bool], etc.).  But
    since Coq's equality operator is polymorphic, these are not the
    only possibilities -- in particular, we can write propositions
    claiming that two _functions_ are equal to each other: *)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

(** In common mathematical practice, two functions [f] and [g] are
    considered equal if they produce the same outputs:

    (forall x, f x = g x) -> f = g

    This is known as the principle of _functional extensionality_. *)

(** Informally speaking, an "extensional property" is one that
    pertains to an object's observable behavior.  Thus, functional
    extensionality simply means that a function's identity is
    completely determined by what we can observe from it -- i.e., in
    Coq terms, the results we obtain after applying it. *)

(** Functional extensionality is not part of Coq's built-in logic.
    This means that some "reasonable" propositions are not provable. *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* Stuck *)
Abort.

(** However, we can add functional extensionality to Coq's core using
    the [Axiom] command. *)

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** Using [Axiom] has the same effect as stating a theorem and
    skipping its proof using [Admitted], but it alerts the reader that
    this isn't just something we're going to come back and fill in
    later! *)

(** We can now invoke functional extensionality in proofs: *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

(** Naturally, we must be careful when adding new axioms into Coq's
    logic, as they may render it _inconsistent_ -- that is, they may
    make it possible to prove every proposition, including [False],
    [2+2=5], etc.!

    Unfortunately, there is no simple way of telling whether an axiom
    is safe to add: hard work by highly-trained trained experts is
    generally required to establish the consistency of any particular
    combination of axioms.

    Fortunately, it is known that adding functional extensionality, in
    particular, _is_ consistent. *)

(** To check whether a particular proof relies on any additional
    axioms, use the [Print Assumptions] command.  *)

Print Assumptions function_equality_ex2.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)

(** **** Exercise: 4 stars, standard (tr_rev_correct)  

    One problem with the definition of the list-reversing function
    [rev] that we have is that it performs a call to [app] on each
    step; running [app] takes time asymptotically linear in the size
    of the list, which means that [rev] has quadratic running time.
    We can improve this with the following definition: *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(** This version is said to be _tail-recursive_, because the recursive
    call to the function is the last operation that needs to be
    performed (i.e., we don't have to execute [++] after the recursive
    call); a decent compiler will generate very efficient code in this
    case.  Prove that the two definitions are indeed equivalent. *)

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Propositions and Booleans *)

(** We've seen two different ways of expressing logical claims in Coq:
    with _booleans_ (of type [bool]), and with _propositions_ (of type
    [Prop]).

    For instance, to claim that a number [n] is even, we can say
    either... *)

(** ... that [evenb n] evaluates to [true]... *)
Example even_42_bool : evenb 42 = true.
Proof. reflexivity. Qed.

(** ... or that there exists some [k] such that [n = double k]. *)
Example even_42_prop : exists k, 42 = double k.
Proof. exists 21. reflexivity. Qed.

(** Of course, it would be pretty strange if these two
    characterizations of evenness did not describe the same set of
    natural numbers!  Fortunately, we can prove that they do... *)

(** We first need two helper lemmas. *)
Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(** **** Exercise: 3 stars, standard (evenb_double_conv)  *)
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  (* Hint: Use the [evenb_S] lemma from [Induction.v]. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

(** In view of this theorem, we say that the boolean computation
    [evenb n] is reflected in the truth of the proposition [exists k,
    n = double k]. *)

(** Similarly, to state that two numbers [n] and [m] are equal, we can
    say either
      - (1) that [n =? m] returns [true], or
      - (2) that [n = m].
    Again, these two notions are equivalent. *)

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.

(** However, even when the boolean and propositional formulations of a
    claim are equivalent from a purely logical perspective, they may
    not be equivalent _operationally_. *)

(** In the case of even numbers above, when proving the
    backwards direction of [even_bool_prop] (i.e., [evenb_double],
    going from the propositional to the boolean claim), we used a
    simple induction on [k].  On the other hand, the converse (the
    [evenb_double_conv] exercise) required a clever generalization,
    since we can't directly prove
    [(evenb n = true) -> (exists k, n = double k)]. *)

(** For these examples, the propositional claims are more useful than
    their boolean counterparts, but this is not always the case.  For
    instance, we cannot test whether a general proposition is true or
    not in a function definition; as a consequence, the following code
    fragment is rejected: *)

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** Coq complains that [n = 2] has type [Prop], while it expects
    an element of [bool] (or some other inductive type with two
    elements).  The reason for this error message has to do with the
    _computational_ nature of Coq's core language, which is designed
    so that every function that it can express is computable and
    total.  One reason for this is to allow the extraction of
    executable programs from Coq developments.  As a consequence,
    [Prop] in Coq does _not_ have a universal case analysis operation
    telling whether any given proposition is true or false, since such
    an operation would allow us to write non-computable functions.

    Although general non-computable properties cannot be phrased as
    boolean computations, it is worth noting that even many
    _computable_ properties are easier to express using [Prop] than
    [bool], since recursive function definitions are subject to
    significant restrictions in Coq.  For instance, the next chapter
    shows how to define the property that a regular expression matches
    a given string using [Prop].  Doing the same with [bool] would
    amount to writing a regular expression matcher, which would be
    more complicated, harder to understand, and harder to reason
    about.

    Conversely, an important side benefit of stating facts using
    booleans is enabling some proof automation through computation
    with Coq terms, a technique known as _proof by
    reflection_.  Consider the following statement: *)

Example even_1000 : exists k, 1000 = double k.

(** The most direct proof of this fact is to give the value of [k]
    explicitly. *)

Proof. exists 500. reflexivity. Qed.

(** On the other hand, the proof of the corresponding boolean
    statement is even simpler: *)

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

(** What is interesting is that, since the two notions are equivalent,
    we can use the boolean formulation to prove the other one without
    mentioning the value 500 explicitly: *)

Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

(** Although we haven't gained much in terms of proof-script
    size in this case, larger proofs can often be made considerably
    simpler by the use of reflection.  As an extreme example, the Coq
    proof of the famous _4-color theorem_ uses reflection to reduce
    the analysis of hundreds of different cases to a boolean
    computation. *)

(** Another notable difference is that the negation of a "boolean
    fact" is straightforward to state and prove: simply flip the
    expected boolean result. *)

Example not_even_1001 : evenb 1001 = false.
Proof.
  (* WORKED IN CLASS *)
  reflexivity.
Qed.

(** In contrast, propositional negation may be more difficult
    to grasp. *)

Example not_even_1001' : ~(exists k, 1001 = double k).
Proof.
  (* WORKED IN CLASS *)
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

(** Equality provides a complementary example: knowing that
    [n =? m = true] is generally of little direct help in the middle
    of a proof involving [n] and [m]; however, if we convert the
    statement to the equivalent form [n = m], we can rewrite with it.
 *)

Lemma plus_eqb_example : forall n m p : nat,
    n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORKED IN CLASS *)
  intros n m p H.
    rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

(** We won't cover reflection in much detail, but it serves as a good
    example showing the complementary strengths of booleans and
    general propositions. *)

(** **** Exercise: 2 stars, standard (logical_connectives)  

    The following lemmas relate the propositional connectives studied
    in this chapter to the corresponding boolean operations. *)

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (eqb_neq)  

    The following theorem is an alternate "negative" formulation of
    [eqb_eq] that is more convenient in certain
    situations (we'll see examples in later chapters). *)

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (eqb_list)  

    Given a boolean operator [eqb] for testing equality of elements of
    some type [A], we can define a function [eqb_list] for testing
    equality of lists with elements in [A].  Complete the definition
    of the [eqb_list] function below.  To make sure that your
    definition is correct, prove the lemma [eqb_list_true_iff]. *)

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Lemma eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, recommended (All_forallb)  

    Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Tactics]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

(** Prove the theorem below, which relates [forallb] to the [All]
    property of the above exercise. *)

Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  (* FILL IN HERE *) Admitted.

(** Are there any important properties of the function [forallb] which
    are not captured by this specification? *)

(* FILL IN HERE 

    [] *)

(* ================================================================= *)
(** ** Classical vs. Constructive Logic *)

(** We have seen that it is not possible to test whether or not a
    proposition [P] holds while defining a Coq function.  You may be
    surprised to learn that a similar restriction applies to _proofs_!
    In other words, the following intuitive reasoning principle is not
    derivable in Coq: *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(** To understand operationally why this is the case, recall
    that, to prove a statement of the form [P \/ Q], we use the [left]
    and [right] tactics, which effectively require knowing which side
    of the disjunction holds.  But the universally quantified [P] in
    [excluded_middle] is an _arbitrary_ proposition, which we know
    nothing about.  We don't have enough information to choose which
    of [left] or [right] to apply, just as Coq doesn't have enough
    information to mechanically decide whether [P] holds or not inside
    a function. *)

(** However, if we happen to know that [P] is reflected in some
    boolean term [b], then knowing whether it holds or not is trivial:
    we just have to check the value of [b]. *)

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

(** In particular, the excluded middle is valid for equations [n = m],
    between natural numbers [n] and [m]. *)

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

(** It may seem strange that the general excluded middle is not
    available by default in Coq; after all, any given claim must be
    either true or false.  Nonetheless, there is an advantage in not
    assuming the excluded middle: statements in Coq can make stronger
    claims than the analogous statements in standard mathematics.
    Notably, if there is a Coq proof of [exists x, P x], it is
    possible to explicitly exhibit a value of [x] for which we can
    prove [P x] -- in other words, every proof of existence is
    necessarily _constructive_. *)

(** Logics like Coq's, which do not assume the excluded middle, are
    referred to as _constructive logics_.

    More conventional logical systems such as ZFC, in which the
    excluded middle does hold for arbitrary propositions, are referred
    to as _classical_. *)

(** The following example illustrates why assuming the excluded middle
    may lead to non-constructive proofs:

    _Claim_: There exist irrational numbers [a] and [b] such that [a ^
    b] is rational.

    _Proof_: It is not difficult to show that [sqrt 2] is irrational.
    If [sqrt 2 ^ sqrt 2] is rational, it suffices to take [a = b =
    sqrt 2] and we are done.  Otherwise, [sqrt 2 ^ sqrt 2] is
    irrational.  In this case, we can take [a = sqrt 2 ^ sqrt 2] and
    [b = sqrt 2], since [a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^
    2 = 2].  []

    Do you see what happened here?  We used the excluded middle to
    consider separately the cases where [sqrt 2 ^ sqrt 2] is rational
    and where it is not, without knowing which one actually holds!
    Because of that, we wind up knowing that such [a] and [b] exist
    but we cannot determine what their actual values are (at least,
    using this line of argument).

    As useful as constructive logic is, it does have its limitations:
    There are many statements that can easily be proven in classical
    logic but that have much more complicated constructive proofs, and
    there are some that are known to have no constructive proof at
    all!  Fortunately, like functional extensionality, the excluded
    middle is known to be compatible with Coq's logic, allowing us to
    add it safely as an axiom.  However, we will not need to do so in
    this book: the results that we cover can be developed entirely
    within constructive logic at negligible extra cost.

    It takes some practice to understand which proof techniques must
    be avoided in constructive reasoning, but arguments by
    contradiction, in particular, are infamous for leading to
    non-constructive proofs.  Here's a typical example: suppose that
    we want to show that there exists [x] with some property [P],
    i.e., such that [P x].  We start by assuming that our conclusion
    is false; that is, [~ exists x, P x]. From this premise, it is not
    hard to derive [forall x, ~ P x].  If we manage to show that this
    intermediate fact results in a contradiction, we arrive at an
    existence proof without ever exhibiting a value of [x] for which
    [P x] holds!

    The technical flaw here, from a constructive standpoint, is that
    we claimed to prove [exists x, P x] using a proof of
    [~ ~ (exists x, P x)].  Allowing ourselves to remove double
    negations from arbitrary statements is equivalent to assuming the
    excluded middle, as shown in one of the exercises below.  Thus,
    this line of reasoning cannot be encoded in Coq without assuming
    additional axioms. *)

(** **** Exercise: 3 stars, standard (excluded_middle_irrefutable)  

    Proving the consistency of Coq with the general excluded middle
    axiom requires complicated reasoning that cannot be carried out
    within Coq itself.  However, the following theorem implies that it
    is always safe to assume a decidability axiom (i.e., an instance
    of excluded middle) for any _particular_ Prop [P].  Why?  Because
    we cannot prove the negation of such an axiom.  If we could, we
    would have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)] (since [P]
    implies [~ ~ P], by the exercise below), which would be a
    contradiction.  But since we can't, it is safe to add [P \/ ~P] as
    an axiom. *)

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (not_exists_dist)  

    It is a theorem of classical logic that the following two
    assertions are equivalent:

    ~ (exists x, ~ P x)
    forall x, P x

    The [dist_not_exists] theorem above proves one side of this
    equivalence. Interestingly, the other direction cannot be proved
    in constructive logic. Your job is to show that it is implied by
    the excluded middle. *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (classical_axioms)  

    For those who like a challenge, here is an exercise taken from the
    Coq'Art book by Bertot and Casteran (p. 123).  Each of the
    following four statements, together with [excluded_middle], can be
    considered as characterizing classical logic.  We can't prove any
    of them in Coq, but we can consistently add any one of them as an
    axiom if we wish to work in classical logic.

    Prove that all five propositions (these four plus
    [excluded_middle]) are equivalent. *)

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

(* FILL IN HERE 

    [] *)

(* Wed Jan 9 12:02:45 EST 2019 *)
