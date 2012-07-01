Require Import Recdef.
Require Import ExtrOcamlNatInt.
Require Import Bool Arith NPeano.
Require Import Coq.Arith.Wf_nat.


Inductive fib_spec : nat -> nat -> Prop :=
| fib_spec1 : fib_spec 0 1
| fib_spec2 : fib_spec 1 2
| fib_spec3 : forall i n m, fib_spec i n -> fib_spec (S i) m -> fib_spec (S (S i)) (n + m).


Fixpoint fib (n:nat) : nat :=
  match n with
  | 0 => 1
  | 1 => 2
  | S (S n'' as n') => fib n'' + fib n'
  end.


Theorem fib_correct : forall i n, fib i = n <-> fib_spec i n.
split.
 generalize dependent n.
 apply (lt_wf_ind i); intros.
 destruct n.
  simpl in H0.
  subst.
  constructor.

  destruct n.
   simpl in H0.
   subst.
   constructor.

   change (fib (S (S n))) with (fib n + fib (S n)) in H0.
   subst.
   constructor.
    apply H.
     auto with arith.

     reflexivity.

    apply H.
     auto with arith.

     reflexivity.

 generalize dependent n.
 apply (lt_wf_ind i); intros.
 destruct n.
  inversion H0.
  reflexivity.

  inversion H0.
   reflexivity.

   change (fib (S (S i0))) with (fib i0 + fib (S i0)).
   replace (fib i0) with n1 .
    replace (fib (S i0)) with m .
     reflexivity.

     symmetry ; apply H.
      subst; auto with arith.

      assumption.

    symmetry ; apply H.
     subst; auto with arith.

     assumption.
Qed.


Parameter bound : nat.


Inductive spec_sub : nat -> nat -> Prop :=
| spec_sub1 : spec_sub 0 0
| spec_sub2 :
  forall i n, spec_sub i n ->
    fib i mod 2 = 0 -> fib i < bound -> spec_sub (S i) (n + fib i)
| spec_sub3 :
  forall i n, spec_sub i n ->
    ~ fib i mod 2 = 0 -> fib i < bound -> spec_sub (S i) n
| spec_sub4 :
  forall i n, spec_sub i n ->
    fib i >= bound -> spec_sub (S i) n.


Definition spec (n:nat) : Prop := forall i, fib i > bound -> spec_sub i n.


Theorem fib_invariant : forall n, fib n + fib (S n) = fib (S (S n)).
destruct n.
 reflexivity.

 destruct n.
  reflexivity.

  reflexivity.
Qed.


Lemma fib_geq1 : forall n, 0 < fib n.
Proof.
induction n; auto.
simpl.
destruct n; auto.
rewrite plus_comm.
apply le_plus_trans.
assumption.
Qed.


Theorem fib_increase_S : forall n, fib n < fib (S n).
Proof.
intro n.
destruct n; auto.
rewrite<- fib_invariant.
change (fib (S n)) with (0 + fib (S n)) in |- * at 1.
apply add_lt_le_mono.
 apply fib_geq1.

 constructor.
Qed.


Theorem fib_increase_le : forall n m, n <= m -> fib n <= fib m.
Proof.
intros n m; generalize dependent n.
induction m.
 inversion 1.
 constructor.

 intros.
 apply le_lt_eq_dec in H.
 destruct H.
  apply le_S_n in l.
  apply le_trans with (fib m).
   apply IHm.
   assumption.

   apply lt_le_weak.
   apply fib_increase_S.

  subst.
  auto.
Qed.


Lemma sub_lt_sub : forall n m l, n > l -> l < m -> n - m < n - l.
Proof.
intros; generalize dependent l; generalize dependent n.
induction m; intros.
 inversion H0.

 destruct n.
  inversion H.

  destruct l.
   simpl.
   unfold lt.
   rewrite <- succ_le_mono.
   rewrite minus_n_O.
   apply minus_le_compat_l.
   apply le_0_n.

   simpl.
   apply IHm; apply lt_S_n; assumption.
Qed.


Lemma sub_neq0__gt : forall n m, n - m <> 0 -> n > m.
Proof.
induction n.
 induction m.
  intro.
  exfalso.
  apply H.
  reflexivity.

  intro.
  exfalso.
  apply H.
  reflexivity.

 intros.
 destruct m.
  apply lt_0_Sn.

  apply lt_n_S.
  apply IHn.
  exact H.
Qed.


Lemma spec_sub_inv_step : forall i n, fib i >= bound -> spec_sub i n -> spec_sub (S i) n.
Proof.
induction i; intros.
 inversion H0.
 apply spec_sub4.
  constructor.

  assumption.

 apply spec_sub4.
  assumption.

  assumption.
Qed.


Lemma spec_sub_inv1 : forall i j n, fib i >= bound -> j >= i -> spec_sub i n -> spec_sub j n.
Proof.
induction j; intros.
 inversion H0.
 subst.
 assumption.

 apply le_lt_eq_dec in H0.
 destruct H0.
  apply spec_sub_inv_step.
   apply le_trans with (fib i).
    assumption.

    apply fib_increase_le.
    auto with arith.

   apply IHj.
    assumption.

    auto with arith.

    assumption.

  subst.
  assumption.
Qed.


Lemma spec_sub_inv2 : forall i j n, fib i >= bound -> j >= i -> spec_sub j n -> spec_sub i n.
Proof.
induction j; intros.
 inversion H0.
 subst.
 assumption.

 apply le_lt_eq_dec in H0.
 destruct H0.
  apply le_S_n in l.
  apply IHj.
   assumption.

   assumption.

   inversion H1; subst.
    exfalso.
    contradict H4.
    apply le_not_lt.
    apply le_trans with (fib i).
     assumption.

     apply fib_increase_le.
     assumption.

    assumption.

    assumption.

  subst.
  assumption.
Qed.



Lemma spec_sub_inv : forall i j n, fib i >= bound -> fib j >= bound -> spec_sub i n -> spec_sub j n.
intros.
destruct (le_ge_dec i j).
 apply spec_sub_inv1 with i; assumption.

 apply spec_sub_inv2 with i; assumption.
Qed.


Fixpoint ble_nat (n:nat) (m:nat) : bool :=
  match n with
  | O => true
  | S n' =>
    match m with
    | O => false
    | S m' => ble_nat n' m'
    end
  end.


Theorem ble_nat_true : forall n m, ble_nat n m = true -> n <= m.
Proof.
induction n; intros.
 destruct m.
  auto.

  auto with arith.

 destruct m.
  inversion H.

  apply le_n_S.
  apply IHn.
  simpl in H.
  assumption.
Qed.


Theorem ble_nat_false : forall n m, ble_nat n m = false -> n > m.
Proof.
induction n; intros.
 inversion H.

 destruct m.
  auto with arith.

  apply lt_n_S.
  apply IHn.
  simpl in H.
  assumption.
Qed.


Fixpoint fib_fast_pre (a:nat) (b:nat) (n:nat) : nat :=
  match n with
  | O => a
  | S n' => fib_fast_pre b (a+b) n'
  end.
Definition fib_fast := fib_fast_pre 1 2.


Lemma fib_fast_pre_correct : forall a b n k,
  fib n = a ->
  fib (S n) = b ->
  fib_fast_pre a b k = fib (k+n).
Proof.
intros a b n k; generalize dependent n; generalize dependent b;
 generalize dependent a.
induction k; intros.
 simpl.
 symmetry ; assumption.

 simpl.
 remember (k + n) as kn.
 destruct kn.
  destruct k.
   destruct n.
    subst; reflexivity.

    inversion Heqkn.

   inversion Heqkn.

  assert (fib (S (S n)) = a + b).
   rewrite <- fib_invariant.
   congruence.

   rewrite IHk with b (a + b) (S n).
    replace (k + S n) with (S (k + n)) .
     rewrite <- Heqkn.
     rewrite fib_invariant.
     reflexivity.

     auto.

    assumption.

    assumption.
Qed.


Theorem fib_fast_correct : forall n, fib n = fib_fast n.
Proof.
intro n.
unfold fib_fast.
rewrite fib_fast_pre_correct with 1 2 0 n; auto.
Qed.


Function f (acc:nat) (n:nat) {measure (fun n => S bound - fib n) n} : nat :=
  let x := fib_fast n in
    if ble_nat bound x
    then acc
    else
      if beq_nat (x mod 2) 0
      then f (acc+x) (S n)
      else f acc (S n).
intros.
apply sub_lt_sub.
 apply lt_le_weak.
 apply lt_n_S.
 apply ble_nat_false.
 rewrite fib_fast_correct.
 assumption.

 apply fib_increase_S.

intros.
apply sub_lt_sub.
 apply lt_le_weak.
 apply lt_n_S.
 apply ble_nat_false.
 rewrite fib_fast_correct.
 assumption.

 apply fib_increase_S.
Defined.


Theorem f_correct_sub : forall acc n, spec_sub n acc -> spec (f acc n).
apply (f_ind (fun acc n m => spec_sub n acc -> spec m)); intros.
 unfold spec; intros.
 apply spec_sub_inv with n.
  apply ble_nat_true.
  rewrite fib_fast_correct.
  assumption.

  auto with arith.

  assumption.

 apply H.
 subst x.
 rewrite<- fib_fast_correct.
 constructor.
  assumption.

  apply beq_nat_true.
  rewrite fib_fast_correct.
  assumption.

  apply ble_nat_false.
  rewrite fib_fast_correct.
  assumption.

 apply H.
 constructor.
  assumption.

  apply beq_nat_false.
  rewrite fib_fast_correct.
  assumption.

  apply ble_nat_false.
  rewrite fib_fast_correct.
  assumption.
Qed.

Definition ans := f 0 0.

Corollary ans_correct : spec ans.
apply f_correct_sub.
constructor.
Qed.

Definition print_int (n:nat) : unit := tt.
Definition main : unit := print_int ans.

Extract Constant modulo => "(mod)".
Extract Constant ble_nat => "(<=)".
Extract Constant print_int => "print_int".
Extract Constant bound => "4_000_000".
Extraction "problem0002.ml" main.
