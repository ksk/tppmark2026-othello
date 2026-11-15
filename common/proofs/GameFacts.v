From Stdlib Require Import List Bool Arith ZArith Lia.
From TPP2026.Common Require Import Rules Game.
Import ListNotations.

(** Playing finite strategies against each other, attainment and uniqueness
    of an exact score, and soundness of optimal play. *)
Module Make (P : Rules.Pieces) (D : Rules.Dimension).
Module G := Game.Make P D.
Include G.
Import P.

Lemma advance_sound : forall b p action b' q,
  advance b p action = Some (b', q) -> transition b p b' q.
Proof.
  intros b p [s|] b' q action_ok; cbn [advance] in action_ok.
  - destruct (play b p s) as [c|] eqn:move_ok; [|discriminate].
    inversion action_ok; subst. eapply transition_move.
    split; [eapply play_in_range; eauto|exact move_ok].
  - destruct (no_moveb b p && negb (no_moveb b (other p))) eqn:pass_ok;
      [|discriminate].
    inversion action_ok; subst.
    apply andb_true_iff in pass_ok as [no_own_move opponent_can_move].
    apply transition_pass.
    + apply no_moveb_spec. exact no_own_move.
    + apply has_moveb_spec. exact opponent_can_move.
Qed.

Theorem replay_sound : forall actions b p b' q,
  replay b p actions = Some (b', q) -> reaches b p b' q.
Proof.
  induction actions as [|action rest IHrest]; intros b p b' q replay_ok;
    cbn [replay] in replay_ok.
  - inversion replay_ok; subst. constructor.
  - destruct (advance b p action) as [[c r]|] eqn:action_ok;
      [|discriminate].
    eapply reaches_step.
    + eapply advance_sound. exact action_ok.
    + eapply IHrest. exact replay_ok.
Qed.

Theorem reaches_preserves_board : forall b p b' q,
  reaches b p b' q -> well_formed b -> well_formed b'.
Proof.
  intros b p b' q legal_play.
  induction legal_play as [b p|b p c q d r step_ok rest_legal IHrest];
    intro board_ok.
  - exact board_ok.
  - apply IHrest.
    exact (transition_preserves_board b p c q board_ok step_ok).
Qed.

Lemma terminal_no_move : forall b, terminal b -> forall p, no_move b p.
Proof. intros b [no_black_move no_white_move] []; assumption. Qed.

Lemma no_move_has_contra : forall b p, no_move b p -> has_move b p -> False.
Proof.
  intros b p no_legal_move [s [c move_legal]].
  exact (no_legal_move s c move_legal).
Qed.

Lemma forces_terminal_goal : forall who goal b p,
  forces who goal b p -> terminal b -> goal b.
Proof.
  intros who goal b p strategy. induction strategy; intro game_over; auto.
  - exfalso. eapply terminal_no_move; eauto.
  - exfalso. eapply no_move_has_contra; [eapply terminal_no_move; eauto|eauto].
Qed.

(** The two quantified strategies can actually be played against each other.
    No separate termination or determinacy axiom is required. *)

Theorem forces_meet : forall g h b p,
  forces Black g b p -> forces White h b p ->
  exists c q, reaches b p c q /\ terminal c /\ g c /\ h c.
Proof.
  intros g h b p black_strategy.
  induction black_strategy as
    [b p game_over black_goal
    |b s b' black_move black_next IHstrategy
    |b white_can_move all_white_moves IHstrategy
    |b p no_own_move opponent_can_move black_next IHstrategy];
    intro white_strategy.
  - exists b, p. split; [constructor|]. split; [exact game_over|]. split;
    [exact black_goal|].
    eapply forces_terminal_goal; eauto.
  - inversion white_strategy as [? ? white_end white_goal|? t d white_move
    white_next|? black_can_move all_black_moves|? ? white_no_move
    white_opponent_can_move white_continue]; subst.
    + exfalso. eapply terminal_no_move; eauto.
    + destruct (IHstrategy (all_black_moves s b' black_move)) as [c [q
      [remaining_play final_facts]]].
      exists c, q. split; [eapply reaches_step; [eapply transition_move;
        exact black_move|exact remaining_play]|exact final_facts].
    + exfalso. eapply white_no_move; eauto.
  - cbn [other] in *.
    inversion white_strategy as [? ? white_end white_goal|? t d white_move
      white_next|? black_can_move all_black_moves|? ? white_no_move
      white_opponent_can_move white_continue]; subst.
    + exfalso. eapply no_move_has_contra; [eapply terminal_no_move;
      eauto|exact white_can_move].
    + destruct (IHstrategy _ _ white_move white_next) as [c [q [remaining_play
      final_facts]]].
      exists c, q. split; [eapply reaches_step; [eapply transition_move;
        exact white_move|exact remaining_play]|exact final_facts].
    + exfalso. eapply no_move_has_contra; eauto.
  - destruct p; cbn [other] in *;
    inversion white_strategy as [? ? white_end white_goal|? t d white_move
    white_next|? black_can_move all_black_moves|? ? white_no_move
    white_opponent_can_move white_continue]; subst.
    + exfalso. eapply no_move_has_contra; [eapply terminal_no_move;
      eauto|exact opponent_can_move].
    + exfalso. eapply no_move_has_contra; eauto.
    + destruct (IHstrategy white_continue) as [c [q [remaining_play
      final_facts]]].
      exists c, q. split; [eapply reaches_step; [apply transition_pass;
        assumption|exact remaining_play]|exact final_facts].
    + exfalso. eapply no_move_has_contra; [eapply terminal_no_move;
      eauto|exact opponent_can_move].
    + exfalso. eapply no_own_move; eauto.
    + destruct (IHstrategy white_continue) as [c [q [remaining_play
      final_facts]]].
      exists c, q. split; [eapply reaches_step; [apply transition_pass;
        assumption|exact remaining_play]|exact final_facts].
Qed.

Theorem bounds_consistent : forall b p lo hi,
  lower_bound b p lo -> upper_bound b p hi -> (lo <= hi)%Z.
Proof.
  intros b p lo hi lower upper.
  destruct (forces_meet _ _ _ _ lower upper) as [c [q [_ [_ [lower_at_end
    upper_at_end]]]]]. lia.
Qed.

Theorem exact_score_attained : forall b p z,
  exact_score b p z -> exists c q,
    reaches b p c q /\ terminal c /\ black_score c = z.
Proof.
  intros b p z [lower upper].
  destruct (forces_meet _ _ _ _ lower upper) as [c [q [legal_play [game_over
    [lower_at_end upper_at_end]]]]].
  exists c, q. split; [exact legal_play|]. split; [exact game_over|]. lia.
Qed.

Theorem exact_score_unique : forall b p z z',
  exact_score b p z -> exact_score b p z' -> z = z'.
Proof.
  intros b p z z' [lower upper] [lower_other upper_other].
  pose proof (bounds_consistent _ _ _ _ lower upper_other).
  pose proof (bounds_consistent _ _ _ _ lower_other upper). lia.
Qed.

Lemma optimal_step : forall z b p action c q rest,
  exact_score b p z -> advance b p action = Some (c, q) ->
  optimal_replay z c q rest -> optimal_replay z b p (action :: rest).
Proof.
  intros z b p action c q rest value_known action_ok rest_optimal. split;
    [exact value_known|]. simpl. now rewrite action_ok.
Qed.

Lemma optimal_end : forall z b p,
  exact_score b p z -> terminal b -> optimal_replay z b p [].
Proof. intros. split; assumption. Qed.

Theorem optimal_replay_sound : forall actions z b p,
  optimal_replay z b p actions -> exists c q,
  replay b p actions = Some (c, q) /\ reaches b p c q /\ terminal c /\
    black_score c = z.
Proof.
  induction actions as [|a rest IHrest];
    intros z b p [value_known rest_optimal].
  - exists b, p. split; [reflexivity|]. split; [constructor|]. split;
    [exact rest_optimal|].
    destruct value_known as [lower upper].
    pose proof (forces_terminal_goal _ _ _ _ lower rest_optimal).
    pose proof (forces_terminal_goal _ _ _ _ upper rest_optimal).
    apply Z.le_antisymm; assumption.
  - simpl in rest_optimal. destruct (advance b p a) as [[d r]|] eqn:action_ok;
    [|contradiction].
    destruct (IHrest _ _ _ rest_optimal) as [c [q [replay_ok [legal_play
      final_facts]]]].
    exists c, q. split.
    + simpl. now rewrite action_ok, replay_ok.
    + split; [eapply reaches_step; [eapply advance_sound;
      exact action_ok|exact legal_play]|exact final_facts].
Qed.

End Make.
