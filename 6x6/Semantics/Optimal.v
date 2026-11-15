From Stdlib Require Import ZArith.
From TPP2026.Proofs.Equivalence Require Import Six.
From TPP2026.Six Require Import Rules Bounds.

(** Use the common strategy theorem for the certificate's score bounds.
    The proof that two strategies can be played against each other is in
    common/proofs/GameFacts.v; it is not repeated for this board size. *)

Theorem exact_score_unique b p z z' :
  Bounds.exact_score b p z -> Bounds.exact_score b p z' -> z = z'.
Proof.
  intros score_z score_z'.
  apply exact_score_agrees in score_z, score_z'.
  exact (Board6.exact_score_unique b p z z' score_z score_z').
Qed.

Print Assumptions exact_score_unique.
