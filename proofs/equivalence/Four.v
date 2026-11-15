From TPP2026.Four Require Import Bounds.
From TPP2026.Boards Require Export Four.

(** The certificate rules and the common rules agree on every board. *)

Theorem play_agrees b p s :
  Board4.play b p s = TPP2026.Four.Rules.play b p s.
Proof. reflexivity. Qed.

Theorem legal_move_agrees :
  Board4.legal_move = TPP2026.Four.Rules.legal_move.
Proof. reflexivity. Qed.

Theorem moves_agree : Board4.moves = TPP2026.Four.Rules.moves.
Proof. reflexivity. Qed.

Theorem no_move_agrees : Board4.no_move = TPP2026.Four.Rules.no_move.
Proof. reflexivity. Qed.

Theorem has_move_agrees : Board4.has_move = TPP2026.Four.Rules.has_move.
Proof. reflexivity. Qed.

Theorem terminal_agrees : Board4.terminal = TPP2026.Four.Rules.terminal.
Proof. reflexivity. Qed.

Theorem count_agrees : Board4.count = TPP2026.Four.Rules.count.
Proof. reflexivity. Qed.

Theorem initial_agrees : Board4.initial = TPP2026.Four.Rules.initial4.
Proof. reflexivity. Qed.

Theorem play_spec b p s b' :
  Board4.play b p s = Some b' <-> Spec4.legal_spec b p s b'.
Proof. exact (Spec4.play_spec b p s b'). Qed.

Theorem white_wins_agrees b p :
  Bounds.white_wins b p <->
  Board4.forces TPP2026.Four.Rules.White Board4.white_ahead b p.
Proof.
  split; intro strategy; induction strategy.
  - now apply Board4.force_end.
  - now eapply Board4.force_choose; eauto.
  - now apply Board4.force_all.
  - now apply Board4.force_pass.
  - now apply Bounds.win_terminal.
  - now eapply Bounds.win_white_move; eauto.
  - now apply Bounds.win_black_moves.
  - now apply Bounds.win_pass.
Qed.

Print Assumptions play_spec.
Print Assumptions white_wins_agrees.
