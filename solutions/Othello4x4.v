From Stdlib Require Import List.
From TPP2026.Boards Require Import Four.
Import ListNotations.

(** 4x4 Othello: can White force a win from the standard initial position?

    See common/README.md for the rules, and common/Rules.v and Game.v for
    the definitions. Place a stone on an empty square and flip every run
    of opposing stones captured in any of the 8 directions. A player with
    no legal move must pass unless neither player can move, when the game
    ends. The player with more stones wins.

         a b c d       B = Black, W = White, . = empty
      1  . . . .       Squares are numbered by row from a1 = 0.
      2  . W B .       Black moves first.
      3  . B W .
      4  . . . .
*)

Definition initial_position : Board4.board :=
  [Empty; Empty; Empty; Empty;
   Empty; Stone White; Stone Black; Empty;
   Empty; Stone Black; Stone White; Empty;
   Empty; Empty; Empty; Empty].

Definition first_player : player := Black.

(** This explicit board is the standard initial position
    from the common rules. *)

Theorem initial_is_standard : initial_position = Board4.initial.
Proof. reflexivity. Qed.

(** Problem: does White have a finite strategy that ends with more stones
    than Black, whatever legal moves Black chooses? The inductive definition
    forces describes finite strategies: choose one own move and handle every
    legal opposing move. *)

Definition problem : Prop :=
  Board4.forces White
    (fun final => Board4.count final Black < Board4.count final White)
    initial_position first_player.

(** Solution: 4x4/ checks the strategy certificate. The equivalence and
    certificate-result proofs in proofs/ express that win in the common
    definitions used above. *)
From TPP2026.Proofs.Certificates Require Import Four.

Theorem solution : problem.
Proof. exact TPP2026.Proofs.Certificates.Four.othello4_white_wins. Qed.

Print Assumptions solution.
