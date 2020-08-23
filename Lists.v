(* Lists *)
Fixpoint eqb (n m : nat) : bool := (* copied from HW_1/2 *)
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.
Notation "x =? y" := (eqb x y) (at level 70).

Module NatList.


Inductive natprod : Type :=
| pair (n1 n2: nat).

Check (pair 3 5).

(* Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute fst(pair 3 4).
*)
Notation "( x , y )" := (pair x y).

(* Compute (fst (3, 5)). *)

Definition fst(p : natprod) : nat :=
  match p with
  |(x, y) => x
  end.

Definition snd(p : natprod) : nat :=
  match p with
  |(x, y) => y
  end.

Compute (fst (3, 5)).
Compute (snd (3, 5)).


Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
  end.

Compute (swap_pair (3,5)).

Theorem surjective_pairing' :
forall n m : nat,
 (n, m) = (fst(n,m), snd(n,m)).
Proof.
simpl. reflexivity.
Qed.

Theorem surjective_pairing :
forall p : natprod,
  p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Theorem snd_fst_is_swap : 
forall p : natprod,
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Theorem fst_swap_is_snd :
forall p : natprod,
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Inductive natlist : Type :=
  |nil
  |cons(n : nat) (l : natlist).

Definition list_3 := cons 3 nil.
Definition list_2_3 := cons 2 list_3.
Definition list_1_2_3 := cons 1 list_2_3.

(* now let's make it more readable *)
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

(* the following function takes a number n and a count and returns a
list of length count with each element equal to n *)
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' =>  n::(repeat n count')
  end.

Compute (repeat 4 10).

Fixpoint length (l : natlist) : nat :=
  match l with
  |nil => O
  |head::tail => S (length tail) (* 1 + length(tail) *)
  end.

Compute (length [1; 2; 3; 4; 5; 6]).

(* appends two lists *)
Fixpoint app(l1 l2 : natlist) : natlist :=
  match l1 with
  |nil => l2
  |head::tail => head::(app tail l2)
  end.

Compute (app [1; 2; 3; 4] [5; 6; 7; 8]).

Notation "x ++ y" := (app x y) (at level 60, right associativity).

(* right associativity means that x~y~z will be read as x~(y~z) instead of (x~y)~z *)

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd(default : nat) (l : natlist) : nat :=
  match l with
  |nil => default
  |head::tail => head
  end.

Definition tl(l : natlist) : natlist :=
  match l with
  |nil => nil
  |head::tail => tail
  end.

Example test_hd_1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd_2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l: natlist) : natlist :=
  match l with
  |nil => nil
  |head::tail => 
    match head with
    |O => nonzeros tail
    |S head' => S head'::(nonzeros tail)
    end
  end.


Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.


Theorem nil_app :
forall l : natlist, [] ++ l = l.
Proof. simpl. reflexivity. Qed.

Theorem tl_length_pred :
forall l : natlist,
pred (length l) = length (tl l).
Proof.
  intros l.
  destruct l as [| head tail].
  -(* l = nil *)
    simpl.
    reflexivity.
  -(* l = head::tail *)
    simpl.
    reflexivity.
Qed.

Theorem app_assoc :
forall l1 l2 l3 : natlist,
(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
intros l1 l2 l3.
induction l1 as [| n l1' IHl1'].
-simpl. reflexivity.
-simpl. rewrite -> IHl1'. reflexivity.
Qed.


Fixpoint rev (l : natlist) : natlist :=
  match l with
  | nil => nil
  | head::tail => rev tail ++ [head]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.


Theorem plus_comm : 
forall n m: nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n IHn'].
    -simpl. rewrite <- plus_n_O. reflexivity.
    -simpl. rewrite <- plus_n_Sm. rewrite -> IHn'. reflexivity. 
(*we use the second function we proved followed by the hypothesis*)
Qed.


Theorem app_length:
forall l1 l2 : natlist,
length (l1++l2) = (length l1) + (length l2).
Proof.
intros l1 l2.
induction l1 as [| n l1' IHl1'].
-simpl. reflexivity.
-simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem rev_length:
forall l : natlist,
length (rev l) = length l.
Proof.
intros l.
induction l as [| n l' IHl'].
-simpl. reflexivity.
-simpl. rewrite app_length. rewrite plus_comm. rewrite -> IHl'.  simpl. reflexivity.
Qed.


(* Homework begins from here *)

Theorem app_nil_r:
forall l : natlist,
l ++ [] = l.
Proof.
intros l.
induction l as [| n l' IHl']. (* we proceed by simple induction *)
-simpl. reflexivity.
-simpl. rewrite -> IHl'. reflexivity. 
Qed.

Theorem rev_app_distr:
forall l1 l2 : natlist, 
rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
intros l1 l2.
induction l1 as [| n l1' IHl1']. (* we proceed by simple induction *)
-simpl. rewrite -> app_nil_r. reflexivity. (* we apply the previous theorem *)
-simpl. rewrite -> IHl1'. rewrite app_assoc. reflexivity. (* we apply the associativity theorem proven earlier. *)
Qed.

Theorem rev_involutive:
forall l : natlist,
rev (rev l) = l.
Proof.
intros l.
induction l as [| n l' IHl'].
-simpl. reflexivity.
-simpl. rewrite rev_app_distr. rewrite -> IHl'. simpl. reflexivity.
(* we apply the previous theorem and the induction hypothesis *)
Qed.


(* a helper function for equality of natural numbers *)
Fixpoint eq_nat (n m : nat) : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => (eq_nat n1 m1)
  end.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1 with
  |nil => (* trivial *)
    match l2 with
    |nil => true
    |head::tail => false
    end
  |head1::tail1 =>
    match l2 with
    |nil => false
    |head2::tail2 => (andb (eq_nat head1 head2) (eqblist tail1 tail2)) 
    (* two lists are equal if their heads and tails are both equal *)
    end
  end.


Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

(*a lemma used in the next theorem *)
Lemma eq_nat_n:
forall n : nat,
eq_nat n n = true. (* eq_nat applied to the same number returns true *)
Proof.
intros n.
induction n as [| n' IHn'].
-simpl. reflexivity.
-simpl. rewrite IHn'. reflexivity.
Qed.

Theorem eqblist_refl : 
forall l : natlist,
true = eqblist l l.
Proof.
intros l.
induction l as [| n l' IHl'].
-simpl. reflexivity. (* nil = nil *)
-simpl. rewrite eq_nat_n. simpl. rewrite <- IHl'. reflexivity.
(* The function will return true if the heads are equal (which they are), we use the lemma. Then we just 
proceed with the hypothesis *)
Qed.

Theorem rev_injective:
forall l1 l2 : natlist,
rev l1 = rev l2 -> l1 = l2.
Proof.
intros l1 l2 condition.
rewrite <- rev_involutive.  (* apply that l2 = rev (rev l2). *)
rewrite <- condition. (* use the condition that rev l2 = rev l1. *)
rewrite -> rev_involutive. (* apply that l1 = rev (rev l1) *)
reflexivity.
Qed.


End NatList. 

Module PartialMap.


Lemma eqb_n:
forall n : nat, eqb n n = true. (* n = n is true *)
Proof.
intros n.
induction n as [| n' IHn'].
-simpl. reflexivity.
-simpl. rewrite -> IHn'. reflexivity.
Qed.


Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Inductive id : Type :=
  | Id (n : nat).


Definition eqb_id (x1 x2 : id) := 
  match x1, x2 with
  |Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl:
forall x, true = eqb_id x x.
Proof.
intros x.
destruct x. simpl. rewrite -> eqb_n. reflexivity. (*we just use the lemma above *)
Qed.


Inductive partial_map : Type :=
|empty
|record (i : id) (v : nat) (m : partial_map).

(* This declaration can be read: There are two ways to construct a partial_map: 
either using the constructor empty to represent an empty partial map, 
or by applying the constructor record to a key, a value, and an existing partial_map
 to construct a partial_map with an additional key-to-value mapping. *)

Definition update (d : partial_map) (x : id) (value : nat) : partial_map :=
  record x value d.
(* update just adds the new (key, value) pair into the hashmap *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  |empty => None
  |record y v d' =>
    if eqb_id x y
    then Some v
    else find x d'
  end.

Theorem update_eq :
forall (d : partial_map) (x : id) (v : nat),
find x (update d x v) = Some v.

Proof.
intros d x v.
simpl. rewrite <- eqb_id_refl. reflexivity. (* we just apply the eqb_id_refl property proven earlier *)
Qed.

Theorem update_neq :
forall (d : partial_map) (x y : id) (o : nat),
eqb_id x y = false -> find x (update d y o) = find x d.

Proof.
intros d x y o condition.
unfold update. (* rewrite update with its definition *)
simpl.
rewrite -> condition. (* use the condition to get to a symmetric claim *) 
reflexivity.
Qed.

End PartialMap.

Module Polymorphism.

(* Polymorphism *)

(* In general, we can use curly braces when defining a parameter to avoid writing the type each time *)
Inductive list (X : Type) : Type :=
|nil
|cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X} _ _.

(* the following function takes a number n and a count and returns a
list of length count with each element equal to n *)
Fixpoint repeat {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | O => nil
  | S count' =>  cons x (repeat x count')
  end.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  |nil => l2
  |cons head tail => cons head (app tail l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  |nil => nil
  |cons head tail => app (rev tail) (cons head nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  |nil => O
  |cons _ tail => S (length tail)
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.
Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.
Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

(* poly_exercises *)
Theorem app_nil_r:
forall (X : Type) (l : list X),
l ++ [] = l.
Proof.
intros X l.
induction l as [| h l' IHl'].
-simpl. reflexivity.
-simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem app_assoc:
forall (A : Type) (l m n : list A),
l ++ m ++ n = (l ++ m) ++ n.
intros A l m n.
induction l as [| h l' IHl'].
-simpl. reflexivity.
-simpl. rewrite <- IHl'. reflexivity.
Qed.

Lemma app_length:
forall (X : Type) (l1 l2 : list X),
length (l1 ++ l2) = length l1 + length l2.
Proof.
intros X l1 l2.
induction l1 as [| h l' IHl'].
-simpl. reflexivity.
-simpl. rewrite IHl'. reflexivity.
Qed.

(* more_poly_exercises *)
Theorem rev_app_distr: 
forall X (l1 l2 : list X),
rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
intros X l1 l2.
induction l1 as [| h l1' IHl1'].
-simpl. rewrite -> app_nil_r. reflexivity.
-simpl. rewrite -> IHl1'. rewrite <- app_assoc. reflexivity.
Qed.

Theorem rev_involutive:
forall (X : Type) (l : list X),
rev (rev l) = l.
Proof.
intros X l.
induction l as [| h l' IHl'].
-simpl. reflexivity.
-simpl. rewrite -> rev_app_distr. simpl. rewrite -> IHl'. reflexivity.
Qed.

(*note: The previous 5 functions were more or less exactly the same as for lists *)

(* functions as data *)
Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Definition doit3times {X:Type} (f : X  -> X) (n:X) : X :=
  f (f (f n)).
Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false. (* negate 3 times *)
Proof. reflexivity. Qed.

Fixpoint filter {X:Type} (test: X -> bool) (l:list X) : (list X) :=
  match l with
  |[] => []
  |h :: t => 
    if test h 
    then h :: (filter test t)
    else filter test t
  end.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.
Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

(* the following function takes [n1, n2 .. nk] and returns [f n1, f n2, .. f nk] *)
Fixpoint map {X Y: Type} (f:X -> Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  |nil => b
  |h :: t => f h (fold f t b )
  end.

Compute fold plus [1;2;3;4] 0.

Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k:nat) => x.
Definition ftrue := constfun true.
Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.
Example constfun_example2 : ftrue 4 = true.
Proof. reflexivity. Qed.

Definition prod_curry {X Y Z : Type} (f : X * Y -> Z) (x : X) (y : Y) : Z :=
 f (x, y).
Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) (p : X*Y) : Z :=
(* p is a pair, and we want to apply the function with the two parameters, so *)
  f (fst p) (snd p).

End Polymorphism.

Module Church.

(* We can represent a natural number n as a function that takes
a function f as a parameter and returns f iterated n times. *)
Definition cnat := 
forall X : Type, (X -> X) -> X -> X. 
(*the first argument is a function, the second argument is a variable, the third is the output *)

Check cnat.

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition three : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f (f x)).

(* church_succ *)
(* n X f x gives the natural number n corresponding to the church numeral. 
To get its successor we apply f on that term. *)
Definition succ (n : cnat) : cnat :=
  fun (X : Type) (f: X -> X) (x : X) => f (n X f x).

Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.
Example succ_2 : succ one = two.
Proof. reflexivity. Qed.
Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

(* church_plus *)
(* m X f x gives the natural number m corresponding to the church numeral. 
Thus, we need to apply f n more times to the number we just got.*)
Definition plus (n m : cnat) : cnat :=
  fun (X : Type) (f: X-> X) (x : X) => (n X f (m X f x)).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3 : plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

(* church_mult *)
(*    n * m = m + m + .. + m is just adding the number m, n times *)
Definition mult (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => (n X (m X f) x).
Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

(* church_exp *)
Definition exp (n m : cnat) : cnat := (* returns n^m *)
  fun (X : Type) (f : X -> X) (x : X) => (m (X -> X) (n X) f) x.
(*source: https://www.ps.uni-saarland.de/courses/sem-ws13/files/notes.pdf *)
(* this was by far the hardest function I had to implement in Coq *)


Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.
Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed.
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.



End Church.

























