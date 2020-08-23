(*basic induction*)
(* all 4 functions, including
commutativity and associativity *)

(* Note: Most of the proofs can easily be deduced by following the example about n = n + 0. *)

Theorem mult_0_r:
forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n IHn'].
    -reflexivity.
    -simpl. rewrite -> IHn'. reflexivity.
Qed.


Theorem plus_n_Sm: 
forall n m: nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n IHn'].
    -simpl. reflexivity.
    -simpl. rewrite -> IHn'. reflexivity.
Qed.

(* taken from the book*)
Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.  Qed.


Theorem plus_comm : 
forall n m: nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n IHn'].
    -simpl. rewrite <- plus_n_O. reflexivity.
    -simpl. rewrite <- plus_n_Sm. rewrite -> IHn'. reflexivity. 
(*we use the second function we proved followed by the hypothesi*)
Qed.

Theorem plus_assoc:
forall  n m p: nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n IHn'].
    -simpl. reflexivity.
    -simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus: 
forall n, double n = n + n.
Proof.
  intros n.
  induction n as [| n IHn'].
    -simpl. reflexivity.
    -simpl. rewrite -> plus_comm. rewrite -> IHn'.  simpl. reflexivity.
Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(*introducing a function from chapter 1 *)
Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.  Qed.

Theorem evenb_S: 
forall n: nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n.
  induction n as [| n IHn'].
    -simpl. reflexivity.
    -rewrite -> IHn'. rewrite -> negb_involutive. simpl. reflexivity. 
Qed.

(* Exercise: 1 star, standard (destruct_induction) *)

(*Briefly explain the difference between the tactics destruct and induction. *)
(* 
We use destruct whenever we want to check cases, i.e. generate subgoals.
Induction also covers checking cases, but of different kinds. Namely, induction also
has a base case that we build everything else upon on using an induction hypothesis.
Thus, everything is build on the base case and the hypothesis, while in destruct, the 
cases are more independent. Induction can be used to prove more robust claims though,
especially for things involving natural numbers, because they are built inductively.
 *)


(* plus_comm_informal *)

(*
Theorem: Addition is a commutative operation, i.e. for any n and m that are natural numbers, n + m = m + n.

Proof: By induction on n.
First, suppose n = 0.
We must show that 0 + n = n + 0. This follows from the fact that 0 + n = n (by definition of addition) and after applying the previously proven theorem plus_n_0.
Next, suppose n = S n', and that n' + m = m + n'.
We must show that S n' + m = m + S n'.
By definition of addition, this is equivalent to S (n' + m) = m + S n'.
Now we apply theorem plus_n_Sm that says that for all n, m; S (n + m) = n + (S m). 
Thus, what we want to prove now is S (n' + m) = S (m + n'). 
By using the induction hypothesis, we equalize the two sides; thus ending the proof.
*)

(* eqb_refl_informal *)
 
Fixpoint eqb (n m : nat) : bool :=
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

(*
Theorem: true = n =? n for any n (or (eqb n n) = true)
Proof:

We induct on n.
First, suppose n = 0. By the definition of eqb, if the two parts we are comparing
are 0, the function returns true, i.e. 0 = 0 is indeed true. 

Now, suppose that n = n for some natural n, i.e. eqb returns true.
We will prove that S n = S n, i.e. the function eqb returns true.

Now, from the definition of the function, we only need to compare the second case of the
second destruct, because we know that we pass the same number as both of the
parameters. Thus, S n = S n returns the same thing as n = n, which by the induction 
hypothis is true. 

The proof is now complete.

*)





















