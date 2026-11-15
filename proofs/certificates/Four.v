From TPP2026.Four Require Import Rules CertificateResult.
From TPP2026.Proofs.Equivalence Require Export Four.

(** Apply the checked 4x4 certificate result to the common game definition. *)

Theorem othello4_white_wins :
  Board4.forces White Board4.white_ahead Board4.initial Black.
Proof.
  apply white_wins_agrees.
  exact CertificateResult.othello4_white_wins.
Qed.
Print Assumptions othello4_white_wins.
