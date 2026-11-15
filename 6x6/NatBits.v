From Stdlib Require Import NArith.

Lemma testbit_nat_succ : forall n i,
  N.testbit_nat n (S i) = N.testbit_nat (N.div2 n) i.
Proof. intros [|[p|p|]] i; reflexivity. Qed.

Lemma testbit_nat_correct : forall i n,
  N.testbit_nat n i = N.testbit n (N.of_nat i).
Proof.
  induction i as [|i IH]; intro n.
  - destruct n as [|[p|p|]]; reflexivity.
  - rewrite Nat2N.inj_succ, N.testbit_succ_r_div2 by apply N.le_0_l.
    rewrite testbit_nat_succ. apply IH.
Qed.
Print Assumptions testbit_nat_correct.
