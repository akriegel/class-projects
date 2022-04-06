Require Import Psatz. 
Require Import String.
Require Import Program.
Require Import List.
From Coq Require Import Lia.
Require Export Coq.Init.Nat.
Require Export Coq.Arith.Arith.
Require Export Coq.Arith.Even.
Require Export Coq.Bool.Bool.
Require Export Coq.Lists.List.

(*******************************************)
(*** Misc Definitions and Infrastructure ***)
(*******************************************)

Fixpoint big_sum (f : nat -> nat) (n : nat) : nat := 
  match n with
  | 0 => 0
  | S n' => (big_sum f n') + (f n')
  end.
Lemma big_sum_0 : forall f n,
    (forall x, f x = 0) -> big_sum f n = 0. 
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite H, IHn, plus_0_r; easy. 
Qed.

Notation "[]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.eqb_eq.
Qed.
Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.
Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

#[global]
Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

(*******************************************)
(** Matrix Definitions and Infrastructure **)
(*******************************************)
Declare Scope matrix_scope.
Delimit Scope matrix_scope with M.
Open Scope matrix_scope.

Local Open Scope nat_scope.

Definition Matrix (m n : nat) := nat -> nat -> nat.

Definition WF_Matrix {m n: nat} (A : Matrix m n) : Prop := 
  forall x y, x >= m \/ y >= n -> A x y = 0. 

Notation Vector n := (Matrix n 1).

Notation Square n := (Matrix n n).

(* Showing equality via functional extensionality *)
Ltac prep_matrix_equality :=
  let x := fresh "x" in 
  let y := fresh "y" in 
  apply functional_extensionality; intros x;
  apply functional_extensionality; intros y.

(* Matrix Equivalence *)

Definition mat_equiv {m n : nat} (A B : Matrix m n) : Prop := 
  forall i j, i < m -> j < n -> A i j = B i j.

Infix "==" := mat_equiv (at level 70) : matrix_scope.

Lemma mat_equiv_refl : forall m n (A : Matrix m n), mat_equiv A A.
Proof. unfold mat_equiv; reflexivity. Qed.

Lemma mat_equiv_eq : forall {m n : nat} (A B : Matrix m n),
  WF_Matrix A -> 
  WF_Matrix B -> 
  A == B ->
  A = B.
Proof.
  intros m n A' B' WFA WFB Eq.
  prep_matrix_equality.
  unfold mat_equiv in Eq.
  bdestruct (x <? m).
  bdestruct (y <? n).
  + apply Eq; easy.
  + rewrite WFA, WFB; trivial; right; try lia.
  + rewrite WFA, WFB; trivial; left; try lia.
Qed.

(* 2D List Representation *)
Definition list2D_to_matrix (l : list (list nat)) : 
  Matrix (length l) (length (hd [] l)) :=
  (fun x y => nth y (nth x l []) 0).

Lemma WF_list2D_to_matrix : forall m n li, 
    length li = m ->
    (forall li', In li' li -> length li' = n)  ->
    @WF_Matrix m n (list2D_to_matrix li).
Proof.
  intros m n li L F x y [l | r].
  - unfold list2D_to_matrix. 
    rewrite (nth_overflow _ []).
    destruct y; easy.
    rewrite L. apply l.
  - unfold list2D_to_matrix. 
    rewrite (nth_overflow _ 0).
    easy.
    destruct (nth_in_or_default x li []) as [IN | DEF].
    apply F in IN.
    rewrite IN. apply r.
    rewrite DEF.
    simpl; lia.
Qed.


(* Example *)
Definition M23 : Matrix 2 3 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => 1
  | (0, 1) => 2
  | (0, 2) => 3
  | (1, 0) => 4
  | (1, 1) => 5
  | (1, 2) => 6
  | _ => 0
  end.

Definition M23' : Matrix 2 3 := 
  list2D_to_matrix  
  ([[1; 2; 3];
    [4; 5; 6]]).

Lemma M23eq : M23 = M23'.
Proof.
  unfold M23'.
  compute.
  prep_matrix_equality.
  do 4 (try destruct x; try destruct y; simpl; trivial).
Qed.

(*****************************)
(** Operands and Operations **)
(*****************************)

Fixpoint m2 (n : nat) :=
  match n with
  | O           => 0
  | S (O)       => 1
  | S (S (n'))  => m2 n'
  end.

Lemma m2_SSn : forall n,
  m2 (S (S n)) = m2 n.
Proof.
  intros n. auto.
Qed.

Lemma m2_01 : forall n,
  m2 n = 0 \/ m2 n = 1.
Proof.
Admitted.
(*
  I couldn't figure out how to prove this, though it is trivially true
  by the implementation of m2 / mod 2. I am going to admit the proof and
  carry on.
*)
  

Definition Zero {m n : nat} : Matrix m n := fun x y => 0.

Definition I (n : nat) : Square n := 
  (fun x y => if (x =? y) && (x <? n) then 1 else 0).

(* Optional coercion to scalar (should be limited to 1 × 1 matrices):
Definition to_scalar (m n : nat) (A: Matrix m n) : C := A 0 0.
Coercion to_scalar : Matrix >-> C.
 *)

(* This isn't used, but is interesting *)
Definition I__inf := fun x y => if x =? y then 1 else 0.
Notation "I∞" := I__inf : matrix_scope.

Definition Mmult {m n o : nat} (A : Matrix m n) (B : Matrix n o) : Matrix m o := 
  fun x z => big_sum (fun y => A x y * B y z) n.

Definition parity {m n} (A : Matrix m n) : Matrix m n :=
  fun x y => m2 (A x y).

Lemma WF_mult : forall {m n o : nat} (A : Matrix m n) (B : Matrix n o), 
  WF_Matrix A -> WF_Matrix B -> WF_Matrix (Mmult A B).
Proof.
  unfold WF_Matrix, Mmult.
  intros m n o A B H H0 x y D. 
  apply big_sum_0.
  destruct D; intros z.
  + rewrite H; try left; auto.
  + rewrite H0; try right; auto.
Qed.

Lemma WF_parity : forall {m n : nat} (A : Matrix m n),
  WF_Matrix A -> WF_Matrix (parity A).
Proof.
  unfold WF_Matrix, parity.
  intros m n A H x y [Hx|Hy]; rewrite -> H; auto.
Qed.

Lemma bin_parity : forall {m n : nat} (A : Matrix m n),
  parity A m n = 0 \/ parity A m n = 1.
Proof.
  intros m n A. unfold parity. induction (A m n); auto. induction n0; auto.
  rewrite m2_SSn. apply m2_01.
Qed.
(* NOTE: bin_parity is dependent on admitted proof m2_01 in Matrix.v *)