From TPP2026.Six Require Import Bounds Replay.
From TPP2026.Boards Require Export Six.

(** The concrete certificate rules agree with the common rules on every
    board, including the move lists used to test passes and game end. *)

Theorem play_agrees b p s :
  Board6.play b p s = TPP2026.Six.Rules.play b p s.
Proof. reflexivity. Qed.

Theorem legal_move_agrees :
  Board6.legal_move = TPP2026.Six.Rules.legal_move.
Proof. reflexivity. Qed.

Theorem moves_agree : Board6.moves = TPP2026.Six.Rules.moves.
Proof. reflexivity. Qed.

Theorem no_move_agrees : Board6.no_move = TPP2026.Six.Rules.no_move.
Proof. reflexivity. Qed.

Theorem has_move_agrees : Board6.has_move = TPP2026.Six.Rules.has_move.
Proof. reflexivity. Qed.

Theorem terminal_agrees : Board6.terminal = TPP2026.Six.Rules.terminal.
Proof. reflexivity. Qed.

(** Rewrite the function before applying it to a concrete bitboard. This
    avoids expanding large integers during type conversion. *)

Theorem count_agrees : Board6.count = TPP2026.Six.Rules.count.
Proof. reflexivity. Qed.

Theorem initial_agrees : Board6.initial = initial6.
Proof. reflexivity. Qed.

Theorem play_spec b p s b' :
  Board6.play b p s = Some b' <-> Spec6.legal_spec b p s b'.
Proof. exact (Spec6.play_spec b p s b'). Qed.

Theorem forces_agree who goal b p :
  Bounds.forces who goal b p <-> Board6.forces who goal b p.
Proof.
  split; intro strategy; induction strategy.
  - now apply Board6.force_end.
  - now eapply Board6.force_choose; eauto.
  - now apply Board6.force_all.
  - now apply Board6.force_pass.
  - now apply Bounds.force_end.
  - now eapply Bounds.force_choose; eauto.
  - now apply Bounds.force_all.
  - now apply Bounds.force_pass.
Qed.

Theorem exact_score_agrees b p z :
  Bounds.exact_score b p z <-> Board6.exact_score b p z.
Proof.
  unfold Bounds.exact_score, Board6.exact_score,
    Bounds.lower_bound, Bounds.upper_bound,
    Board6.lower_bound, Board6.upper_bound.
  now rewrite !forces_agree.
Qed.

Theorem replay_agrees b p actions :
  Board6.replay b p actions = Replay.replay b p actions.
Proof. reflexivity. Qed.

Print Assumptions play_spec.
Print Assumptions forces_agree.
