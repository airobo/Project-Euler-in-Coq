Require Import ExtrOcamlNatInt.
Require Import Bool Arith NPeano.

Inductive spec : nat -> nat -> Prop :=
| spec1 : spec 0 0
| spec2 : forall n r, n mod 3 = 0 -> spec n r -> spec (S n) (n + r)
| spec3 : forall n r, n mod 5 = 0 -> spec n r -> spec (S n) (n + r)
| spec4 : forall n r, n mod 3 <> 0 -> n mod 5 <> 0 -> spec n r -> spec (S n) r.

Fixpoint f (n:nat) : nat :=
  match n with
  | O => 0
  | S n' =>
      let r := f n' in
        if beq_nat (n' mod 3) 0 || beq_nat (n' mod 5) 0
        then n' + r
        else r
  end.

Theorem f_correct : forall n r, f n = r -> spec n r.
induction n; intros.
 simpl in H.
 subst.
 constructor.

 simpl in H.
 destruct (eq_nat_dec (n mod 3) 0).
  apply beq_nat_true_iff in e.
  rewrite e in H.
  simpl in H.
  subst.
  apply spec2.
   apply beq_nat_true_iff; assumption.

   apply IHn; reflexivity.

  destruct (eq_nat_dec (n mod 5) 0).
   apply beq_nat_true_iff in e.
   rewrite e in H.
   rewrite orb_true_r in H.
   subst.
   apply spec3.
    apply beq_nat_true_iff; assumption.

    apply IHn; reflexivity.

   apply spec4; try assumption.
   apply IHn.
   rewrite <- H.
   apply beq_nat_false_iff in n0.
   apply beq_nat_false_iff in n1.
   rewrite n0, n1.
   reflexivity.
Qed.

Variable bound : nat.

Definition ans := f bound.

Corollary ans_correct : spec bound ans.
apply f_correct.
reflexivity.
Qed.

Definition print_int (n:nat) : unit := tt.
Definition main : unit := print_int ans.

Extract Constant print_int => "print_int".
Extract Constant bound => "1_000".
Extraction "problem0001.ml" main.
