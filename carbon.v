(*Inductive bit : Type :=
  | bit_zero
  | bit_one
.

Check (0, true).

Require Import Bool.

Definition is_zero b :=
	match b with
  | bit_zero => true
  | bit_one => false
  end
.
Definition is_one b := negb (is_zero b).

Example test_is_zero_zero: is_zero bit_zero = true.
Proof. simpl. reflexivity. Qed.
Example test_is_zero_one: is_zero bit_one = false.
Proof. simpl. reflexivity. Qed.
Example test_is_one_zero: is_one bit_zero = false.
Proof. simpl. reflexivity. Qed.
Example test_is_one_one: is_one bit_one = true.
Proof. simpl. reflexivity. Qed.


Inductive byte : Type :=
  | bits (b0 b1 b2 b3 b4 b5 b6 b7: bit)
.


Inductive memory_block : Type :=
  | block (addresses: list nat).
*)


Inductive Lifetime : Type :=
  | lifetime (start_index end_index: nat).

Require Import Coq.Init.Datatypes.

Definition outlives a b :=
  match a, b with
  | lifetime a_start a_end, lifetime b_start b_end
  	=> andb (a_start < b_start) (b_end < a_end)
  end
.

Check outlives.
