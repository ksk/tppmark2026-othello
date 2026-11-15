From Stdlib Require Import List NArith.
From TPP2026.Six Require Import Rules Dag.
Import ListNotations.

Fixpoint decode_bits (fuel : nat) (bb wb : N) : board :=
  match fuel with
  | O => []
  | S n =>
    (if N.odd bb then Stone Black else if N.odd wb then Stone White else Empty)
             :: decode_bits n (N.div2 bb) (N.div2 wb)
  end.

Lemma testbit_zero_odd : forall n, N.testbit n 0 = N.odd n.
Proof. intros [|[p|p|]]; reflexivity. Qed.

Lemma decode_bits_correct : forall fuel bb wb,
  decode_bits fuel bb wb = map (fun i =>
    if N.testbit bb (N.of_nat i) then Stone Black
    else if N.testbit wb (N.of_nat i) then Stone White else Empty) (seq 0 fuel).
Proof.
  induction fuel as [|n IH]; intros bb wb; [reflexivity|].
  cbn [decode_bits seq map]. rewrite !testbit_zero_odd. f_equal.
  rewrite IH. rewrite <- (seq_shift n 0), map_map.
  apply map_ext. intro i. rewrite Nat2N.inj_succ.
  rewrite !N.testbit_succ_r_div2 by apply N.le_0_l. reflexivity.
Qed.

Definition fast_claim_board (c : claim) : board :=
  decode_bits 36 (black_bits c) (white_bits c).

Theorem fast_claim_board_correct : forall c, fast_claim_board c = claim_board c.
Proof.
  intro c. unfold fast_claim_board, claim_board, squares.
  apply decode_bits_correct.
Qed.
Print Assumptions fast_claim_board_correct.
