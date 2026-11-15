From Stdlib Require Import List ZArith.
From TPP2026.Boards Require Import Six.
Import ListNotations.

(** 6x6 Othello: what is the optimal score of the standard initial position?

    See common/README.md for the rules, and common/Rules.v and Game.v for
    the definitions. Place a stone on an empty square and flip every run
    of opposing stones captured in any of the 8 directions. A player with
    no legal move must pass unless neither player can move, when the game
    ends. The player with more stones wins.

         a b c d e f       B = Black, W = White, . = empty
      1  . . . . . .       Squares are numbered by row from a1 = 0.
      2  . . . . . .       Black moves first.
      3  . . W B . .
      4  . . B W . .
      5  . . . . . .
      6  . . . . . .
*)

Definition initial_position : Board6.board :=
  [Empty; Empty; Empty; Empty; Empty; Empty;
   Empty; Empty; Empty; Empty; Empty; Empty;
   Empty; Empty; Stone White; Stone Black; Empty; Empty;
   Empty; Empty; Stone Black; Stone White; Empty; Empty;
   Empty; Empty; Empty; Empty; Empty; Empty;
   Empty; Empty; Empty; Empty; Empty; Empty].

Definition first_player : player := Black.

(** This explicit board is the standard initial position
    from the common rules. *)

Theorem initial_is_standard : initial_position = Board6.initial.
Proof. reflexivity. Qed.

(** Problem: the score is the final black stone count minus the white count.
    Can Black guarantee at least -4 against every White response, and can
    White guarantee at most -4 against every Black response?
    These two finite strategies establish an optimal score of -4. *)

Definition problem : Prop :=
  Board6.forces Black (fun final => (-4 <= Board6.black_score final)%Z)
    initial_position first_player /\
  Board6.forces White (fun final => (Board6.black_score final <= -4)%Z)
    initial_position first_player.

(** Solution: 6x6/ checks the lower and upper bound certificates. The
    equivalence and certificate-result proofs in proofs/ express those
    bounds in the common definitions used above. *)
From TPP2026.Proofs.Certificates Require Import Six.

Theorem solution : problem.
Proof. exact TPP2026.Proofs.Certificates.Six.initial6_exact_minus_four. Qed.

(** Consequences: White can force a win, and the optimal score is unique. *)

Corollary white_wins :
  Board6.forces White
    (fun final => Board6.count final Black < Board6.count final White)
    initial_position first_player.
Proof. exact TPP2026.Proofs.Certificates.Six.initial6_white_wins. Qed.

Corollary value_unique : forall z,
  Board6.exact_score initial_position first_player z -> z = (-4)%Z.
Proof. exact TPP2026.Proofs.Certificates.Six.initial6_value_unique. Qed.

(** An optimal game

    One optimal game, with 32 placements and no passes. Coordinates run
    from left to right, then down, starting at the top left.
    c2 b4 c5 d2 e4 e3 d1 c1 b1 d5 d6 f4 b3 b2 f3 f2
    e2 b6 a4 a3 a5 a6 a1 a2 f1 c6 e1 e6 f5 b5 e5 f6
    Each move preserves the optimal score. The final counts are 16 black
    stones and 20 white stones. *)

Definition optimal_actions : list (option nat) :=
  map (@Some nat)
    [8; 19; 26; 9; 22; 16; 3; 2; 1; 27; 33; 23; 13; 7; 17; 11;
     10; 31; 18; 12; 24; 30; 0; 6; 5; 32; 4; 34; 29; 25; 28; 35].

Theorem optimal_line :
  Board6.optimal_replay (-4) initial_position first_player optimal_actions /\
  exists final turn,
    Board6.replay initial_position first_player optimal_actions =
      Some (final, turn) /\
    Board6.terminal final /\
    Board6.count final Black = 16 /\ Board6.count final White = 20.
Proof.
  split.
  - exact TPP2026.Proofs.Certificates.Six.optimal_actions_are_optimal.
  - exact TPP2026.Proofs.Certificates.Six.optimal_actions_finish_20_16.
Qed.

(** All optimal games

    Every optimal game has final score -4. This theorem does not fix the
    individual stone counts for all optimal games. *)

Corollary every_optimal_line_has_score_minus_four : forall actions z,
  Board6.optimal_replay z initial_position first_player actions ->
  exists final turn,
    Board6.replay initial_position first_player actions = Some (final, turn) /\
    Board6.terminal final /\ Board6.black_score final = (-4)%Z.
Proof. exact TPP2026.Proofs.Certificates.Six.initial6_optimal_outcome. Qed.
