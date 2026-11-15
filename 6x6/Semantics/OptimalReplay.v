From Stdlib Require Import List ZArith.
From TPP2026.Proofs.Equivalence Require Import Six.
From TPP2026.Six Require Import Rules Bounds Replay.
From TPP2026.Six.Semantics Require Import Optimal.
Import ListNotations.

(** A game in which both players play optimally uses the common definition.
    These small lemmas accept the score bounds checked by the certificates. *)

Definition optimal_replay := Board6.optimal_replay.

Lemma optimal_step z b p action c q rest :
  Bounds.exact_score b p z -> advance b p action = Some (c, q) ->
  optimal_replay z c q rest -> optimal_replay z b p (action :: rest).
Proof.
  intros score_z action_ok rest_optimal.
  apply exact_score_agrees in score_z.
  exact (Board6.optimal_step z b p action c q rest
    score_z action_ok rest_optimal).
Qed.

Lemma optimal_end z b p :
  Bounds.exact_score b p z -> terminal b -> optimal_replay z b p [].
Proof.
  intros score_z game_over.
  apply exact_score_agrees in score_z.
  exact (Board6.optimal_end z b p score_z game_over).
Qed.

Theorem optimal_replay_sound actions z b p :
  optimal_replay z b p actions -> exists c q,
    replay b p actions = Some (c, q) /\ reaches b p c q /\
    terminal c /\ black_score c = z.
Proof.
  intro play_optimal.
  destruct (Board6.optimal_replay_sound actions z b p play_optimal)
    as [c [q [replay_ok [_ outcome]]]].
  exists c, q.
  split; [exact replay_ok |].
  split; [exact (Replay.replay_sound actions b p c q replay_ok) |].
  exact outcome.
Qed.

Print Assumptions optimal_replay_sound.
