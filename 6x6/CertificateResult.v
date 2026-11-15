From Stdlib Require Import ZArith Lia.
From TPP2026.Proofs.Equivalence Require Import Six.
From TPP2026.Six Require Import Rules Bounds Replay InitialSymmetry.
From TPP2026.Six.Semantics Require Import Optimal OptimalReplay.
From TPP2026.Six.InitialLower Require Import Result.
From TPP2026.Six.InitialUpper Require Import Result.

(** Compile only after BOTH complete certificate assemblies exist.
    The four initial black moves are covered by proved board symmetries. *)

Theorem initial6_exact_minus_four : exact_score initial6 Black (-4).
Proof.
  split.
  - exact TPP2026.Six.InitialLower.Result.result.
  - apply initial_upper_from_first8.
    exact TPP2026.Six.InitialUpper.Result.result.
Qed.

Corollary initial6_white_wins_exact : forces White white_ahead initial6 Black.
Proof.
  destruct initial6_exact_minus_four as [_ upper].
  eapply forces_weaken; [|exact upper].
  intros b white_bound. unfold black_score in white_bound. unfold white_ahead.
  lia.
Qed.

Corollary initial6_value_unique : forall z,
  exact_score initial6 Black z -> z = (-4)%Z.
Proof.
  intros z score_eq. eapply exact_score_unique;
    [exact score_eq|exact initial6_exact_minus_four].
Qed.

Corollary initial6_optimal_outcome : forall actions z,
  optimal_replay z initial6 Black actions -> exists c q,
  replay initial6 Black actions = Some (c, q) /\ terminal c /\
    black_score c = (-4)%Z.
Proof.
  intros actions z play_optimal.
  assert (score_eq : z = (-4)%Z) by
    (apply initial6_value_unique; apply exact_score_agrees;
     destruct actions; exact (proj1 play_optimal)).
  subst z.
  destruct (optimal_replay_sound _ _ _ _ play_optimal) as [c [q [replay_ok [_
    [game_over final_score]]]]].
  exists c, q. split; [exact replay_ok|]. split; assumption.
Qed.
