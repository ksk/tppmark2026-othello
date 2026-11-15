From Stdlib Require Import List ZArith.
From TPP2026.Six Require Import Rules CertificateResult OptimalPlay.
From TPP2026.Proofs.Equivalence Require Export Six.

(** Express the checked 6x6 certificate results in the common game
    definition, using the equivalences proved in [Equivalence.Six]. *)

Theorem initial6_exact_minus_four : Board6.exact_score Board6.initial Black
  (-4).
Proof.
  apply exact_score_agrees.
  exact CertificateResult.initial6_exact_minus_four.
Qed.

Corollary initial6_white_wins :
  Board6.forces White Board6.white_ahead Board6.initial Black.
Proof.
  apply forces_agree.
  exact CertificateResult.initial6_white_wins_exact.
Qed.

Corollary initial6_value_unique : forall z,
  Board6.exact_score Board6.initial Black z -> z = (-4)%Z.
Proof.
  intros z score_eq.
  eapply Board6.exact_score_unique;
    [exact score_eq|exact initial6_exact_minus_four].
Qed.

(** Coordinates use a1 = 0; moves alternate Black, White, without a pass:
    c2 b4 c5 d2 e4 e3 d1 c1 b1 d5 d6 f4 b3 b2 f3 f2
    e2 b6 a4 a3 a5 a6 a1 a2 f1 c6 e1 e6 f5 b5 e5 f6. *)

Definition optimal_actions := OptimalPlay.meeting_actions.

Theorem optimal_actions_are_optimal :
  Board6.optimal_replay (-4) Board6.initial Black optimal_actions.
Proof.
  exact OptimalPlay.meeting_is_optimal.
Qed.

Theorem optimal_actions_finish_20_16 : exists c q,
  Board6.replay Board6.initial Black optimal_actions = Some (c, q) /\
  Board6.terminal c /\ Board6.count c Black = 16 /\ Board6.count c White = 20.
Proof.
  exists OptimalPlay.position32, Black.
  split; [exact OptimalPlay.meeting_replay_checked|].
  split.
  - split; apply Board6.no_moveb_spec; vm_compute; reflexivity.
  - rewrite TPP2026.Proofs.Equivalence.Six.count_agrees.
    exact OptimalPlay.meeting_final_counts.
Qed.

Theorem initial6_optimal_20_16 : exists actions c q,
  Board6.optimal_replay (-4) Board6.initial Black actions /\
  Board6.replay Board6.initial Black actions = Some (c, q) /\
  Board6.terminal c /\ Board6.count c Black = 16 /\ Board6.count c White = 20.
Proof.
  destruct optimal_actions_finish_20_16 as [c [q play_optimal]].
  exists optimal_actions, c, q. split;
    [exact optimal_actions_are_optimal|exact play_optimal].
Qed.

Corollary initial6_optimal_outcome : forall actions z,
  Board6.optimal_replay z Board6.initial Black actions -> exists c q,
  Board6.replay Board6.initial Black actions = Some (c, q) /\
  Board6.terminal c /\ Board6.black_score c = (-4)%Z.
Proof.
  intros actions z play_optimal.
  assert (score_eq : z = (-4)%Z) by
    (apply initial6_value_unique; destruct actions; exact (proj1 play_optimal)).
  subst z.
  destruct (Board6.optimal_replay_sound _ _ _ _ play_optimal)
    as [c [q [replay_ok [_ [game_over final_score]]]]].
  exists c, q. split; [exact replay_ok|]. split; assumption.
Qed.
