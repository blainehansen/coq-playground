Module NatPlayground.

	Inductive nat : Type :=
		| O
		| S (n : nat).

	Definition pred (n : nat) : nat :=
	match n with
		| O => O
		| S n' => n'
	end.

End NatPlayground.

(*Check (S (S (S (S O)))).*)

Definition minustwo (n : nat) : nat :=
	match n with
		| O => O
		| S O => O
		| S (S n') => n'
	end.

(*Compute (minustwo 4).

Check S.
Check pred.
Check minustwo.*)


Fixpoint evenb (n:nat) : bool :=
	match n with
	| O => true
	| S O => false
	| S (S n') => evenb n'
	end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.


Module NatPlayground2.

	Fixpoint plus (n : nat) (m : nat) : nat :=
		match n with
			| O => m
			| S n' => S (plus n' m)
		end.

	(*Compute (plus 3 2).*)

	Fixpoint mult (n m : nat) : nat :=
		match n with
			| O => O
			| S n' => plus m (mult n' m)
		end.
	Example test_mult1: (mult 3 3) = 9.
	Proof. simpl. reflexivity. Qed.

	Fixpoint minus (n m : nat) : nat :=
		match n, m with
		| O , _ => O
		| S _ , O => n
		| S n', S m' => minus n' m'
		end.

End NatPlayground2.


Fixpoint exp (base power : nat) : nat :=
	match power with
		| O => S O
		| S p => mult base (exp base p)
	end.


Fixpoint factorial (n : nat) : nat :=
	match n with
	| O => 1
	| S n' => mult n (factorial n')
	end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.


Notation "x + y" := (plus x y)
	(at level 50, left associativity)
	: nat_scope.
Notation "x - y" := (minus x y)
	(at level 50, left associativity)
	: nat_scope.
Notation "x * y" := (mult x y)
	(at level 40, left associativity)
	: nat_scope.

(*Check ((0 + 1) + 1).*)


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


Fixpoint leb (n m : nat) : bool :=
	match n with
	| O => true
	| S n' =>
		match m with
		| O => false
		| S m' => leb n' m'
		end
	end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.


Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.


Definition ltb (n m : nat) : bool :=
	match minus m n with
	| O => false
	| S r => true
	end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.


Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
	intros n. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
	intros n. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
	intros n. reflexivity. Qed.


Theorem plus_id_example : forall n m:nat,
	n = m ->
	n + n = m + m.

Proof.
	(* move both quantifiers into the context: *)
	intros n m.
	(* move the hypothesis into the context: *)
	intros H.
	(* rewrite the goal using the hypothesis: *)
	rewrite -> H.
	reflexivity. Qed.


Theorem plus_id_exercise : forall n m o : nat,
	n = m -> m = o -> n + m = m + o.
Proof.
	intros n m o.
	intros H.
	intros H'.
	rewrite -> H.
	rewrite <- H'.
	reflexivity. Qed.


Theorem mult_0_plus : forall n m : nat,
	(0 + n) * m = n * m.
Proof.
	intros n m.
	rewrite -> plus_O_n.
	reflexivity. Qed.



Theorem mult_S_1 : forall n m : nat,
	m = S n ->
	m * (1 + n) = m * m.
Proof.
	intros n m.
	intros H.
	rewrite -> plus_1_l.
	rewrite -> H.
	reflexivity. Qed.


(*Theorem plus_1_neq_0_firsttry : forall n : nat,
	(n + 1) =? 0 = false.
Proof.
	intros n.
	simpl. (* does nothing! *)
Abort.


Theorem plus_1_neq_0 : forall n : nat,
	(n + 1) =? 0 = false.
Proof.
	intros n. destruct n as [| n'] eqn:E.
	- reflexivity.
	- reflexivity.
	Qed.



Theorem negb_involutive : forall b : bool, negb (negb b) = b.
Proof.
  intros b.
  destruct b eqn:E.
  - reflexivity.
  - reflexivity.
  Qed.*)


(*
Theorem andb_true_elim2 : forall b c : bool, andb b c = true -> c = true.
Proof.
	intros b c. destruct b, c eqn:E.
	- intros H1. reflexivity.
	- intros H2. reflexivity.
	- intros H3. reflexivity.
	- intros H4. reflexivity.
	Qed.
*)
