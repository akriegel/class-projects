Require Import Matrix.
From Coq Require Import Lia.
(*
  The following constant definitions correspond to Hamming Code being proven.
  Providing other values should allow this .v file to prove codes beyond the
  Hamming(7,4)
*)
(* Hamming(7,4) values *)
Definition H74_WS : nat := 4. (* Word Size *)
Definition H74_CS : nat := 7. (* Code Size *)
Definition H74_CGM : Matrix 4 7 := (* Code Generator Matrix *)
  list2D_to_matrix
  ([
    [1;1;1;0;0;0;0];
    [1;0;0;1;1;0;0];
    [0;1;0;1;0;1;0];
    [1;1;0;1;0;0;1]
  ]).
Definition H74_PCM : Matrix 7 3 := (* Parity Check Matrix *)
  list2D_to_matrix
  ([
    [1;0;0];
    [0;1;0];
    [1;1;0];
    [0;0;1];
    [1;0;1];
    [0;1;1];
    [1;1;1]
  ]).
Definition H74_DCM : Matrix 7 4 := (* Decoder Matrix *)
  list2D_to_matrix
  ([
    [0;0;0;0];
    [0;0;0;0];
    [1;0;0;0];
    [0;0;0;0];
    [0;1;0;0];
    [0;0;1;0];
    [0;0;0;1]
  ]).
(* End Hamming(7,4) Values *)

(* Constant assignment (here to Hamming(7,4)) *)
Definition WS : nat := H74_WS.
Definition CS : nat := H74_CS.
Definition SS : nat := CS - WS. (* Syndrome (parity bit vector) Size *)
Definition Max_Word : nat := 2 ^ WS.
Definition Code_Generator_Matrix : Matrix WS CS := H74_CGM.
Definition Parity_Check_Matrix : Matrix CS SS := H74_PCM.
Definition Decoder_Matrix : Matrix CS WS := H74_DCM.
Check Code_Generator_Matrix.
Check Parity_Check_Matrix.
Check Decoder_Matrix.

Notation Word := (Matrix 1 WS).
Definition WF_Word (W : Word) : Prop :=
  WF_Matrix W /\ forall y, W 1 y = 0 \/ W 1 y = 1.

Notation Code := (Matrix 1 CS).
Definition WF_Code (C : Code) : Prop :=
  WF_Matrix C /\ forall y, C 1 y = 0 \/ C 1 y = 1.

Notation Synd := (Matrix 1 SS).
Definition WF_Synd (S : Synd) : Prop :=
  WF_Matrix S /\ forall y, S 1 y = 0 \/ S 1 y = 1.

Ltac mat_solve x y :=
  do 8 (try destruct x; try destruct y; simpl; trivial; try lia).

Lemma CGM_WF : WF_Matrix Code_Generator_Matrix.
Proof. unfold WF_Matrix. intros x y [H|H]; compute in H; mat_solve x y. Qed.

Lemma PCM_WF : WF_Matrix Parity_Check_Matrix.
Proof. unfold WF_Matrix. intros x y [H|H]; compute in H; mat_solve x y. Qed.

Lemma DCM_WF : WF_Matrix Decoder_Matrix.
Proof. unfold WF_Matrix. intros x y [H|H]; compute in H; mat_solve x y. Qed.

(* Basic Binary definitions and operators (from Basics.v and Induction.v) *)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z     => B1 Z
  | B0 m' => B1 m'
  | B1 m' => B0 (incr m')
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z     => 0
  | B0 m' => 2 * (bin_to_nat m')
  | B1 m' => 1 + 2 * (bin_to_nat m')
  end.

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O      => Z
  | S (n') => incr(nat_to_bin n')
  end.

(* digify inputs a binary number and nat and outputs an n bit binary number
   truncates most significant bits or adds trailing zeroes *)
Fixpoint digify (b : bin) (n : nat) : bin :=
  match n with
  | O      => Z
  | S (n') => match b with
              | Z     => B0 (digify (B0 Z) n')
              | B0 b' => B0 (digify b' n')
              | B1 b' => B1 (digify b' n')
              end
  end.

Example dig_test1 :
  (digify Z 4) = B0 (B0 (B0 (B0 Z))).
Proof. reflexivity. Qed.

Example dig_test2 :
  (digify (B1 Z) 4) = B1 (B0 (B0 (B0 Z))).
Proof. reflexivity. Qed.

Example dig_test3 :
  (digify (B1 Z) 0) =  Z.
Proof. reflexivity. Qed.

Example dig_test4 :
  (digify (B0 (B1 (B0 (B1 Z)))) 3) =  B0 (B1 (B0 Z)).
Proof. reflexivity. Qed.

Example dig_test5 :
  (digify (B1 (B1 (B0 (B1 Z)))) 4) =  B1 (B1 (B0 (B1 Z))).
Proof. reflexivity. Qed.

(* takes a binary number and outputs a nat list with its digits *)
Fixpoint bin_to_list (b : bin) : list(nat) :=
  match b with
  | Z     => []
  | B0 b' => 0 :: (bin_to_list b')
  | B1 b' => 1 :: (bin_to_list b')
  end.

Example btl_test1 :
  bin_to_list (B0 (B1 Z)) = [0 ; 1].
Proof. reflexivity. Qed.

Example btl_test2 :
  bin_to_list Z = [].
Proof. reflexivity. Qed.

Example btl_test3 :
  bin_to_list (B1 (B1 (B0 (B1 Z)))) = [1 ; 1 ; 0 ; 1].
Proof. reflexivity. Qed.

(* transforms a nat into a WS-digit binary word vector *)
Definition nat_to_word (n : nat) : Word :=
  list2D_to_matrix [(bin_to_list (digify (nat_to_bin n) WS))].

(* All WS-bit binary nats make well-formed words *)
Lemma nat_to_word_WF : forall n,
  n < Max_Word -> WF_Word (nat_to_word n).
Proof. intros n Hn. compute in Hn. unfold WF_Word. split.
  - unfold WF_Matrix. intros x y [H|H]; compute in H;
    do 16 (try destruct n; mat_solve x y).
  - intros x. left. mat_solve x y.
Qed.

Definition W1 : Word :=
  fun x y => 
  match (x, y) with
  | (0, 0) => 0
  | (0, 1) => 1
  | (0, 2) => 1
  | (0, 3) => 0
  | _ => 0
  end.

Definition W1' : Word :=
  nat_to_word 6.

Lemma ntw_test1 : W1 = W1'.
Proof.
  unfold W1'. prep_matrix_equality. mat_solve x y.
Qed.

Definition W2 : Word :=
  fun x y => 
  match (x, y) with
  | (0, 0) => 1
  | (0, 1) => 1
  | (0, 2) => 1
  | (0, 3) => 1
  | _ => 0
  end.
 
Definition W2' : Word :=
  nat_to_word 15.

Lemma ntw_test2 : W2 = W2'.
Proof.
  unfold W2'. prep_matrix_equality. mat_solve x y.
Qed.

(* Generates a code from an input word *)
Definition word_to_code (W : Word) : Code :=
  parity (Mmult W Code_Generator_Matrix).

(* Codes generated from well-formed Words are well-formed
   NOTE: This proof depends on an admitted proof in Matrix.v
    This lemma turned out to be unneeded for formally proving the
    Hamming(7,4) code, but because it was part of what I explored I
    am leaving it in as an extra informally proven fact. *)
Lemma word_to_code_WF : forall W,
  WF_Word W ->
  WF_Code (word_to_code W).
Proof.
  intros W [H1 H2]. unfold WF_Code. split.
  - unfold word_to_code. apply WF_parity. apply WF_mult. apply H1. apply CGM_WF.
  - intros y. unfold word_to_code. 
    assert (H: forall {m n} (A : Matrix m n), parity A m n = 0 \/ parity A m n = 1).
    { intros m n A. apply bin_parity. }
    apply H with (n := y).
Qed. (* DoAP m2_01 *)

(* combines above functions to form a code directly from an input nat n *)
Definition nat_to_code (n : nat) : Code :=
  word_to_code (nat_to_word n).

Definition Code_0 : Code :=
  list2D_to_matrix
  ([[0;0;0;0;0;0;0]]).

Definition Code_0' : Code :=
  nat_to_code 0.

Lemma ntc_test0 :
  Code_0 = Code_0'.
Proof.
  unfold Code_0'. prep_matrix_equality. mat_solve x y.
Qed.

Definition Code_12 : Code :=
  list2D_to_matrix
  ([[1;0;0;0;0;1;1]]).

Definition Code_12' : Code :=
  nat_to_code 12.

Lemma ntc_test12 :
  Code_12 = Code_12'.
Proof.
  unfold Code_12'. prep_matrix_equality. mat_solve x y.
Qed.

(* Generates a Syndrome vector from a given Code.
   This will be used to error-check the Code.*)
Definition code_to_synd (C : Code) : Synd :=
  parity (Mmult C Parity_Check_Matrix).
(* Synds generated from well-formed Codes are well-formed
   NOTE: Dependent on Admitted Proof. See word_to_code_WF above *)
Lemma code_to_synd_WF : forall C,
  WF_Code C -> WF_Synd (code_to_synd C).
Proof.
  intros C [H1 H2]. unfold WF_Synd. split.
  - unfold code_to_synd. apply WF_parity. apply WF_mult. apply H1. apply PCM_WF.
  - intros y.
    assert (H: forall {m n} (A : Matrix m n), parity A m n = 0 \/ parity A m n = 1).
    { intros m n A. apply bin_parity. }
    apply H with (n := y).
Qed. (* DoAP m2_01 *)

(* converts Vector of length n to binary (requires an input bin Z to start) *)
Fixpoint vect_to_bin (n : nat) (V : Vector n) (b : bin) : bin :=
  match n with
  | O      => b
  | S (n') => match (V 0 n') with
              | 1 => (vect_to_bin n' V (B1 b))
              | _ => (vect_to_bin n' V (B0 b))
              end
  end.

(* Determines the erroneous bit if there is a one-bit error
   + returns 0 if there are no errors
   + returns n if the nth bit is erroneous (matrix index n-1) *)
Definition bit_err (S : Synd) : nat :=
  bin_to_nat (vect_to_bin SS S Z).

Example be0 : bit_err Zero = 0.
Proof. reflexivity. Qed.

Example be5 : bit_err (list2D_to_matrix([[1;0;1]])) = 5.
Proof. reflexivity. Qed.

Example be6 : bit_err (list2D_to_matrix([[0;1;1]])) = 6.
Proof. reflexivity. Qed.

(* Flips the nth bit of input code C
   + returns C unchanged if bit 0 is to be flipped
   + returns C with nth bit (index n-1) flipped otherwise
   NOTE: used to simulate errors AND correct them *)
Definition flip_bit_at_n (C : Code) (n : nat) :=
  match n with
  | O      => C
  | S (n') =>
    fun x y => if (y =? n') && (x =? 0) then if (C x y) =? 1 then 0 else 1
      else if (C x y) =? 1 then 1 else 0
  end.

Definition t_flip_0s_4 : Code :=
  list2D_to_matrix
  ([
    [0;0;0;1;0;0;0]
  ]).

Example test_flip_null_4 :
  t_flip_0s_4 = flip_bit_at_n Zero 4.
Proof. prep_matrix_equality. mat_solve x y. Qed.

Definition t_flip_1s : Code :=
  list2D_to_matrix
  ([
    [1;1;1;1;1;1;1]
  ]).

Definition t_flip_1s_6 : Code :=
  list2D_to_matrix
  ([
    [1;1;1;1;1;0;1]
  ]).

Example test_flip_1s_6 :
  t_flip_1s_6 = flip_bit_at_n t_flip_1s 6.
Proof. unfold t_flip_1s_6. simpl. prep_matrix_equality. mat_solve x y. Qed.

(* flipping none of the bits yields the input code *)
Lemma flip_0_refl : forall C,
  C = flip_bit_at_n C 0.
Proof. reflexivity. Qed.

(* takes a code, corrects one-bit error by flipping the nth bit
   + nth bit found by generating syndrome vector of C
   + returns C unchanged if no error is detected *)
Definition bit_err_fix (C : Code) : Code :=
  flip_bit_at_n C (bit_err (code_to_synd C)).

(* decodes a word from a code *)
Definition code_to_word (C : Code) : Word :=
  (Mmult C Decoder_Matrix).

Example nat_code_word1 :
  code_to_word (nat_to_code 1) = list2D_to_matrix ([[1;0;0;0]]).
Proof. prep_matrix_equality. mat_solve x y. Qed.

(* Generating a code from a nat and decoding it to a word yields the
   same code as the one generated directly from the nat *)
Lemma nat_code_word : forall n,
  n < Max_Word ->
  code_to_word (nat_to_code n) = nat_to_word n.
Proof.
  intros n H. compute in H.
  do 16 (destruct n; try prep_matrix_equality; mat_solve x y; try lia).
Qed.

(* converts a word back to a nat *)
Definition word_to_nat (W : Word) : nat :=
  bin_to_nat (vect_to_bin WS W Z).

(* This Lemma shows that all 16 nats in our word size
   can be encoded and decoded accurately *)
Lemma nat_code_nat : forall n,
   n < Max_Word ->
   word_to_nat (code_to_word (nat_to_code n)) = n.
Proof.
   intros n H. compute in H. do 16 (destruct n; auto; try lia).
Qed.

(* 1-bit errors in codes can be simulated by the flip_bit_at_n function.
   A Code is 1-bit error safe (bit_err_safe) if the code can recover from
   any one of its bits being flipped via bit_err_fix *)
Definition bit_err_safe (C : Code) : Prop :=
  forall (i : nat),
  i < 8 -> bit_err_fix (flip_bit_at_n C i) = C.

(* tactic to check all possible one-bit errors for showing bit_err_safe holds *)
Ltac check_code_safe i x y :=
  do 8 (destruct i; only 1: mat_solve x y; try lia).

(* Example case showing the code generated from 0 is 1-bit error safe *)
Lemma code0_safe : bit_err_safe (nat_to_code 0).
Proof.
  unfold bit_err_safe. intros i H. prep_matrix_equality.
  check_code_safe i x y.
Qed.

(*
  -- Big Bad Proof --
  The following proof takes about 75 seconds on my machine. It verifies,
  for nat n < 16, that the code generated by nat_to_code n is 1-bit error
  safe. bit_err_safe is the Prop that holds iff a code can be returned to
  its original state via bit_err_fix for any 1-bit error. The proof shows
  the Hamming(7,4) code holds for all cases in its scope. It can detect
  and correct any 1-bit error on any 4-bit unsigned integer.
*)
Lemma Hamming74_Formal_Proof : forall n,
  n < 16 ->
  bit_err_safe (nat_to_code n).
Proof.
  unfold bit_err_safe. intros n Hn i Hi.
  prep_matrix_equality.
  do 16 (destruct n; only 1: check_code_safe i x y; try lia).
Qed.

(*
  Given the lemmas dependent on the admitted proof are NOT used in any
  of the components of this last proof, it is safe to say that the
  Hamming(7,4) code has hereby been formally proven in the coq proof assistant.

  This was the primary goal of my project, and I am very glad to have been
  able to show this. I attempted to design my functions in a way that would
  scale to other Hamming codes. Were I to revisit this project I would continue
  by proving the Hamming(7,4) can detect (but not correct) any 2 bit error with
  an extra 8th parity bit, before examining differently sized Hamming codes.
*)