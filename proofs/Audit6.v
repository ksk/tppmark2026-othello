From TPP2026.Solutions Require Import Othello6x6.
From TPP2026.Six.LinkExp Require Import BoundedAudit.

(** Audit the 6x6 solution theorems and every dependency down to the saved
    certificate leaves for assumptions. *)
Ltac2 Eval audit_closed_many [
  "TPP2026.Solutions.Othello6x6.solution";
  "TPP2026.Solutions.Othello6x6.white_wins";
  "TPP2026.Solutions.Othello6x6.value_unique";
  "TPP2026.Solutions.Othello6x6.optimal_line";
  "TPP2026.Solutions.Othello6x6.every_optimal_line_has_score_minus_four"
].
