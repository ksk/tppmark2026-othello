From Stdlib Require Import List Bool Arith.
From TPP2026.Six Require Import Rules Bounds Dag FastDecode BitRules BitDag.
Import ListNotations.

(** A bounded search may fail to find a strategy; returning true always
    constructs a finite strategy for the original list-board rules. *)

Fixpoint endgame (fuel : nat) who goalb c p : bool :=
  match fuel with
  | O => false
  | S rest =>
    match bit_moves c p with
    | [] => if bit_no_moveb c (other p) then goalb (fast_claim_board c)
            else endgame rest who goalb c (other p)
    | ms => if same_player p who
            then existsb (fun sc =>
              endgame rest who goalb (snd sc) (other p)) ms
            else forallb (fun sc =>
              endgame rest who goalb (snd sc) (other p)) ms
    end
  end.

Lemma bit_member_legal : forall c p s d,
  In (s, d) (bit_moves c p) -> legal_move (claim_board c) p s (claim_board d).
Proof.
  intros c p s d H. apply moves_spec. rewrite <- bit_moves_correct.
  apply in_map_iff. exists (s, d). split; [reflexivity|exact H].
Qed.

Lemma different_player : forall p who, same_player p who = false ->
  p = other who.
Proof. destruct p, who; simpl; intros; congruence. Qed.

Theorem endgame_sound : forall fuel who goalb goal,
  (forall b, goalb b = true -> goal b) -> forall c p,
  endgame fuel who goalb c p = true -> forces who goal (claim_board c) p.
Proof.
  induction fuel as [|fuel IH]; intros who goalb goal Hgoal c p H;
    [discriminate|].
  cbn [endgame] in H.
  destruct (bit_moves c p) as [|[s d] ms] eqn:E.
  - assert (Hnone : no_move (claim_board c) p).
    { apply no_moveb_spec. rewrite <- bit_no_moveb_correct. unfold bit_no_moveb.
    now rewrite E. }
    destruct (bit_no_moveb c (other p)) eqn:Eother.
    + rewrite bit_no_moveb_correct in Eother. apply no_moveb_spec in Eother.
      apply force_end.
      * destruct p; simpl in *; split; assumption.
      * apply Hgoal. now rewrite fast_claim_board_correct in H.
    + apply force_pass; [exact Hnone| |eapply IH; eauto].
      apply has_moveb_spec. rewrite <- bit_no_moveb_correct, Eother.
      reflexivity.
  - assert (Hsome : has_move (claim_board c) p).
    { exists s, (claim_board d). apply bit_member_legal. rewrite E. simpl; auto.
    }
    destruct (same_player p who) eqn:Ep.
    + apply same_player_true in Ep. subst p.
      apply existsb_exists in H as [[t d'] [Hin Hchild]].
      eapply force_choose.
      * apply bit_member_legal. rewrite E. exact Hin.
      * eapply IH; eauto.
    + apply different_player in Ep. subst p. rewrite other_other in H.
      apply force_all; [exact Hsome|]. intros t b' Hlegal.
      apply moves_spec in Hlegal. rewrite <- bit_moves_correct, E in Hlegal.
      apply in_map_iff in Hlegal as [[t' d'] [Heq Hin]]. simpl in Heq.
      inversion Heq; subst t' b'.
      apply forallb_forall with (x := (t, d')) in H; [|exact Hin].
      eapply IH; eauto.
Qed.
Print Assumptions endgame_sound.
