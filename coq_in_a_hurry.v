Check True.

Check False.

Check 3.

Check (3+4).

Check (3=5).

Check (3,4).

Check ((3=5)/\True).

Check nat -> Prop.

Check (3 <= 6).

Check (3,3=5):nat * Prop.

Check (fun x:nat => x = 3).

Check (forall x:nat, x < 3 \/ (exists y:nat, x = y + 3)).

Locate "_ <= _".

Check and.

Eval compute in
  let f := fun x => (x * 3, x) in f 3.

Definition sum3 := fun x1: nat => fun x2: nat => fun x3: nat => x1 + x2 + x3. 
Definition sum4 (x1: nat) (x2: nat) (x3: nat) (x4: nat) := x1 + x2 + x3 + x4.

Eval compute in
  sum3 1 2 3.

Eval compute in
  sum4 2 3 4.

Definition example1 := fun x : nat => x*x+2*x+1.

Reset example1.

Definition example1 (x : nat) := x*x+2*x+1.

Eval compute in
  example1 1.

Require Import Bool.

Eval compute in
  if true then 3 else 6.

Search bool.

Require Import Arith.

Definition is_zero (n:nat) :=
  match n with
    0 => true
  | (S p) => false
  end.

Eval compute in
  is_zero 0.

Eval compute in
  is_zero 10.

Print pred.
Print Init.Nat.pred.

Fixpoint sum_n n :=
  match n with
    0 => 0
  | S p => p + sum_n p
  end.

Eval compute in
  sum_n 5.

Fixpoint sum_n2 (n: nat) (s: nat) :=
  match n with
    0 => s
  | S p => sum_n2 p (p + s)
  end.

Eval compute in
  sum_n2 5 6.

Fixpoint evenb n :=
  match n with
    0 => true
  | 1 => false
  | S (S p) => evenb p
  end.

Eval compute in
  evenb 4.

Eval compute in
  evenb 5.

Require Import List.

Check 1::2:: 3 :: nil.

Check nil.

Check (nil : list nat).

Eval compute in
  map (fun x => x + 3) (1::2::3::nil).

Fixpoint listnn n :=
  match n with
    0 => (nil : list nat)
  | S p => 0 :: map (fun x => x + 1) (listnn p)
  end.

Eval compute in
  listnn 3.

Eval compute in
  listnn 0.

Eval compute in
  listnn 7.

Definition head_evb l :=
  match l with
    nil => false
  | (a::tl) => evenb a
  end.

Eval compute in
  head_evb (5 :: 4 :: nil).

Fixpoint sum_list l :=
  match l with
    nil => 0
  | (a::tl) => a + sum_list tl
  end.

Eval compute in
  sum_list (1::2::3::nil).

Fixpoint insert n l :=
  match l with
    nil => (n :: nil)
  | (h::tl) => if leb n h then n :: h :: tl else h :: (insert n tl)
  end.

Eval compute in
  insert 5 (1 :: 6 :: 7 :: nil).

Fixpoint sort l :=
  match l with
    nil => nil
  | (h :: tl) => insert h (sort tl)
  end.

Eval compute in
  sort (1 :: 6 :: 3 :: 0 :: nil).

Definition first_sorted l :=
  match l with
    nil => true
  | (h :: nil) => true
  | (h1 :: h2 :: tl) => leb h1 h2
  end.

Eval compute in
  first_sorted (1 :: 3 :: nil).


Fixpoint is_sorted l :=
  match l with
    nil => true
  | (h :: tl) => (andb (first_sorted l) (is_sorted tl))
  end.

Eval compute in
  is_sorted (1 :: 3 :: 7 :: 0 :: nil).

Fixpoint count_list l n :=
  match l with
    nil => 0
  | (h :: tl) =>
      let c := if beq_nat h n then 1 else 0
      in c + count_list tl n
  end.

Eval compute in
  count_list (1 :: 1 :: 2 :: 2 :: 3 :: 1 :: nil) 2.

(* Search True. *)

(* Search le. *)

(* SearchPattern (_ + _ <= _ + _). *)

(* SearchRewrite (_ + (_ - _)). *)

(* SearchAbout leb. *)

Lemma example2 : forall a b: Prop, a /\ b -> b /\ a.
Proof.
  intros a b H.
  split.
  destruct H as [H1 H2].
  exact H2.
  intuition.
Qed.

Lemma example3 : forall A B, A \/ B -> B \/ A.
Proof.
  intros A B H.
  destruct H as [H1 | H2].
  right; exact H1.
  left; exact H2.
Qed.

Check le_n.
Check le_S.

Lemma example4: 3 <= 5.
apply le_S.
apply le_S.
apply le_n.
Qed.

Check le_trans.

Lemma example5: forall x y, x <= 10 -> 10 <= y -> x <= y.
intros x y x10 y10.
apply le_trans with (n := x) (m := 10) (p := y).
exact x10.
exact y10.
Qed.

Lemma example6: forall x y, (x + y) * (x + y) = x*x + 2*x*y + y*y.
intros x y.
SearchRewrite (_ * (_ + _)).
rewrite mult_plus_distr_l.
rewrite mult_plus_distr_r.
rewrite mult_plus_distr_r.
SearchRewrite (_ + (_ + _)).
rewrite plus_assoc.
SearchRewrite (_ * _).
rewrite Nat.mul_comm with (n := y) (m := x).
SearchRewrite (S _ * _).
pattern (x * y) at 1; rewrite <- Nat.mul_1_l.
rewrite <- plus_assoc with (n := x * x).
rewrite <- Nat.mul_succ_l.
SearchRewrite (_ * ( _ * _)).
rewrite Nat.mul_assoc with (n := 2).
reflexivity.
Qed.

Require Import Omega.
Lemma omega_example: 
  forall f x y,
  0 < x 
  -> 0 < f x 
  -> 3 * f x <= 2 * y 
  -> f x <= y.
intros.
omega.
Qed.

Lemma omega_exercise_1:
  forall A B C: Prop,
  A /\ (B /\ C)
  -> (A /\ B) /\ C.
intros.
split.
split.
destruct H as [HA HBC].
exact HA.
destruct H as [HA HBC].
destruct HBC as [HB HC].
exact HB.
destruct H as [HA HBC].
destruct HBC as [HB HC].
exact HC.
Qed.

Lemma omega_exercise_2:
  forall A B C D: Prop,
  (A->B) /\ (C->D) /\ A /\ C
  -> B
  -> D.
  intros a b c d H HB.
  destruct H as [AB rest].
  destruct rest as [CD ac].
  destruct ac as [HA HC].
  apply CD.
  apply HC.
Qed.

Lemma omega_exercise_3:
  forall A: Prop,
  ~(A/\~A).
intros A.
unfold not.
intros.
destruct H as [HA HAF].
apply HAF.
exact HA.
Qed.

Lemma omega_exercise_4:
  forall A B C: Prop,
  A \/ (B \/ C)
  -> (A \/ B) \/ C.
intros.
case H.
  intros HA; left; left; exact HA.
intros HBC.
case HBC.
  intros HB; left; right; exact HB.
  intros HC; right; exact HC.
Qed.

Require Import Bool.

Lemma omega_exercise_5:
  forall A B: Prop,
  (A \/ B) /\ ~A
  -> B.
intros.
destruct H. 
case H.
intros.
elim H0.
exact H1.
intros.
exact H1.
Qed.

Lemma sum_n_p : forall n, 2 * sum_n n + n = n * n.
Proof.
induction n.
  - unfold sum_n.
    unfold mult.
    unfold plus.
    reflexivity.
  - assert (SnSn : S n * S n = n * n + 2 * n + 1).
    ring.
    rewrite SnSn.
    rewrite <- IHn.
    simpl sum_n.
    SearchRewrite (_ * (_ + _)).
    rewrite Nat.mul_add_distr_l.
    SearchRewrite (_ + _).
    rewrite Nat.add_comm with (n := 2 *n) (m := 2 * sum_n n).
    SearchRewrite (_ + (_ + _)).
    ring.
Qed.

Lemma evenb_p:
  forall n,
  evenb n = true 
  -> exists x, n = 2 * x.
  assert (Main:
    forall n,
    (evenb n = true
     -> exists x, n = 2 * x)
    /\
    (evenb (S n) = true
    -> exists x, S n = 2 * x)).
  induction n.
    - split.
      * exists 0.
        ring.
      * unfold evenb.
        intros.
        discriminate H.
    - split.
      * destruct IHn.
        exact H0.
      * simpl.
        destruct IHn.
        intros.
        assert (x2: exists x, n = 2 * x).
        apply H.
        exact H1.
        destruct x2 as [x q].
        exists (x + 1).
        rewrite q.
        ring.
    - intros n evb.
      destruct (Main n) as [H _].
      apply H.
      exact evb.
Qed.

Fixpoint add n m := 
  match n with 
    0 => m
    | S p => add p (S m)
  end.

(* add (S n) m = add n (S m). *)
(* S (add (S n) m) = S (add n (S m)). *)
(* add (S n) m = S (add n m) *)
(* S (add (S n) m) = S (S (add n m)) *)

Check f_equal.

Lemma liftLeftS:
  forall n m,
  add n (S m) = S (add n m).
Proof.
induction n.
  - unfold add.
    reflexivity.
  - simpl.
    intros.
    rewrite IHn with (m := (S m)).
    reflexivity.
Qed.

Lemma liftRightS:
  forall n m,
  add (S n) m = S (add n m).
Proof.
induction n.
  - unfold add.
    reflexivity.
  - intros.
    simpl.
    rewrite liftLeftS.
    reflexivity.
Qed.

Lemma addplus:
  forall n m,
  add n m = n + m.
induction n.
  - intros.
    simpl.
    reflexivity.
  - intros.
    rewrite liftRightS.
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

Fixpoint sum_odd_n (n: nat): nat :=
  match n with
  | 0 => 0
  | S p => 1 + 2 * p + sum_odd_n p
  end.

Lemma sum_odd_n2:
  forall n: nat,
  sum_odd_n n = n*n.
Proof.
induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    Search (_ + 0).
    rewrite <- plus_n_O.
    Search (_ * (S _)).
    rewrite Nat.mul_succ_r.
    Search (_ + _).
    rewrite Nat.add_comm with (n := (n * n)).
    Search (_ + (_ + _)).
    rewrite Nat.add_assoc.
    reflexivity.
Qed.

Fixpoint count n l :=
  match l with
  | nil => 0
  | a::tl => if beq_nat n a then 1+count n tl else count n tl
  end.

Lemma insert_incr:
  forall n l,
  count n (insert n l) = 1 + count n l.
induction l.
  - simpl.
    SearchAbout beq_nat.
    rewrite Nat.eqb_refl.
    reflexivity.
  - simpl.
    case (Nat.leb n a).
      * simpl.
        rewrite Nat.eqb_refl.
        reflexivity.
      * simpl.
        rewrite IHl.
        case (beq_nat n a).
          -- SearchRewrite (_ + _).
             rewrite Nat.add_comm.
             SearchRewrite (S (_)).
             rewrite Nat.add_1_r.
             reflexivity.
          -- rewrite Nat.add_1_l.
             reflexivity.
Qed.

Inductive bin : Type :=
  | L : bin
  | N : bin -> bin -> bin
.

Check L.

Check (N L L).

Inductive ex61 : Type :=
  | C : nat -> ex61
  | T : nat -> ex61 -> ex61 -> ex61
  | F : bool -> ex61 -> ex61 -> ex61 -> ex61
.

Check T 1 (F true (C 1) (C 2) (C 3)) (C 4).

Definition example7 (t : bin): bool :=
  match t with
    N L L => false
  | _ => true
  end.

Fixpoint flatten_aux (t1 t2: bin) : bin :=
  match t1 with
    L => N L t2
  | N t'1 t'2 => flatten_aux t'1 (flatten_aux t'2 t2)
  end.

Fixpoint flatten (t: bin) : bin :=
  match t with
    L => L
  | N t1 t2 => flatten_aux t1 (flatten t2)
  end
.

Fixpoint size (t: bin) : nat :=
  match t with
    L => 1
  | N t1 t2 => 1 + size t1 + size t2
  end.

Eval compute in
  flatten_aux (N L L) L.

Lemma example7_size:
  forall t, example7 t = false -> size t = 3.
intros t.
destruct t.
  - simpl.
    intros.
    discriminate H.
  - destruct t1.
    destruct t2.
    * simpl.
      intros.
      reflexivity.
    * intros.
      simpl.
      discriminate H.
    * simpl.
      intros.
      discriminate H.
Qed.

Lemma flatten_aux_size:
  forall t1 t2
  , size (flatten_aux t1 t2) = size t1 + size t2 + 1.
induction t1.
  - intros. simpl. 
    Search (_ + _).
    rewrite Nat.add_comm.
    SearchRewrite (1 + _).
    rewrite Nat.add_1_l with (n := (size t2)).
    reflexivity.
  - simpl.
    intros.
    rewrite IHt1_1.
    rewrite IHt1_2.
    ring.
Qed.

Lemma flatten_size:
  forall t,
  size (flatten t) = size t.
induction t.
  - simpl.
    reflexivity.
  - simpl.
    rewrite flatten_aux_size.
    rewrite IHt2.
    ring.
Qed.

Lemma not_subterm_self_1:
  forall x y,
  ~ x = N x y.
induction x.
  intros y; discriminate.
  intros y abs.
  injection abs.
  intros.
  assert (HH: x1 <> N x1 x2).
  apply IHx1.
  case HH.
  exact H0.
Qed.

Print nat.

Fixpoint nat_fact (n : nat): nat :=
  match n with
    0 => 1
  | S p => S p * nat_fact p
  end.

Fixpoint fib (n: nat) : nat :=
  match n with
    0 => 0
  | S q =>
      match q with
        0 => 1
      | S p => fib p + fib q
      end
  end.

Inductive even : nat -> Prop :=
  even0: even 0
  | evenS : forall x: nat, even x -> even (S (S (x))).

Lemma even_mult:
  forall x, even x -> exists y, x = 2 * y.
Proof.
intros.
elim H.
  - exists 0.
    reflexivity.
  - intros.
    destruct H1 as [y Heq].
    rewrite Heq.
    exists (S y).
    ring.
Qed.




















  
  
  






