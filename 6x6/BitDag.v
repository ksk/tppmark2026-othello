From Stdlib Require Import List Bool NArith ZArith.
From TPP2026.Six Require Import Rules Bounds Dag FastDecode BitRules.
Import ListNotations.

Definition bit_reference (env : trie claim) (c : claim) p id :=
  match lookup id env with
  | None => false
  | Some d =>
    N.eqb (black_bits c) (black_bits d) && N.eqb (white_bits c) (white_bits d)
              && same_player p (claim_turn d)
  end.

Lemma bit_reference_sound : forall who goal env,
  trie_all (valid_claim who goal) env -> forall c p id,
  bit_reference env c p id = true -> forces who goal (claim_board c) p.
Proof.
  intros who goal env Henv [bb wb q] p id H. unfold bit_reference in H.
  destruct (lookup id env) as [[bb' wb' q']|] eqn:E; [|discriminate].
  apply andb_true_iff in H as [Hbits Hp].
  apply andb_true_iff in Hbits as [Hb Hw].
  apply N.eqb_eq in Hb. apply N.eqb_eq in Hw. apply same_player_true in Hp.
  simpl in *. subst bb' wb' p.
  exact (lookup_all claim (valid_claim who goal) env Henv id (Claim bb wb q')
    E).
Qed.

Definition bit_node who goalb (env : trie claim) c op :=
  let p := claim_turn c in
  match op with
  | DEnd =>
    bit_no_moveb c Black && bit_no_moveb c White && goalb (fast_claim_board c)
  | DChoose s child => if same_player p who then
      match bit_play c who s with None => false
      | Some d => bit_reference env d (other who) child end else false
  | DAll children => if same_player p (other who) then
      match bit_moves c (other who) with
      | [] => false
      | ms => check_all (fun mc child =>
        bit_reference env (snd mc) who child) ms children
      end else false
  | DPass child => bit_no_moveb c p && negb (bit_no_moveb c (other p)) &&
                  bit_reference env c (other p) child
  end.

Theorem bit_node_sound : forall who goalb goal,
  (forall b, goalb b = true -> goal b) -> forall env c op,
  trie_all (valid_claim who goal) env -> bit_node who goalb env c op = true ->
    valid_claim who goal c.
Proof.
  intros who goalb goal Hgoal env c op Henv H. unfold valid_claim.
  destruct op as [|s child|children|child]; cbn [bit_node] in H.
  - rewrite !bit_no_moveb_correct, fast_claim_board_correct in H.
    apply andb_true_iff in H as [Hmoves Hscore].
    apply andb_true_iff in Hmoves as [Hb Hw].
    apply force_end; [split; apply no_moveb_spec; assumption|auto].
  - destruct (same_player (claim_turn c) who) eqn:Hp; [|discriminate].
    apply same_player_true in Hp. rewrite Hp.
    destruct (bit_play c who s) as [d|] eqn:E; [|discriminate].
    pose proof (bit_play_correct c who s) as Ep. rewrite E in Ep. simpl in Ep.
    symmetry in Ep.
    eapply force_choose.
    + split; [eapply play_in_range; exact Ep|exact Ep].
    + eapply bit_reference_sound; eauto.
  - destruct (same_player (claim_turn c) (other who)) eqn:Hp; [|discriminate].
    apply same_player_true in Hp. rewrite Hp.
    destruct (bit_moves c (other who)) as [|[s d] rest] eqn:E; [discriminate|].
    apply force_all.
    + exists s, (claim_board d). apply moves_spec.
      rewrite <- bit_moves_correct, E. simpl. auto.
    + intros t b' Hlegal. apply moves_spec in Hlegal.
      rewrite <- bit_moves_correct, E in Hlegal.
      apply in_map_iff in Hlegal as [[s' d'] [Heq Hin]]. simpl in Heq.
      inversion Heq; subst s' b'.
      destruct (check_all_member _ _ _ _ _ H (t, d') Hin) as [id Hid].
      eapply bit_reference_sound; eauto.
  - rewrite !bit_no_moveb_correct in H.
    apply andb_true_iff in H as [Hpass Hchild].
    apply andb_true_iff in Hpass as [Hnone Hsome].
    apply force_pass.
    + apply no_moveb_spec. exact Hnone.
    + apply has_moveb_spec. exact Hsome.
    + eapply bit_reference_sound; eauto.
Qed.

Fixpoint bit_run who goalb entries (env : trie claim) : option (trie claim) :=
  match entries with
  | [] => Some env
  | e :: rest => if bit_node who goalb env (entry_claim e) (entry_op e)
      then bit_run who goalb rest (insert (entry_id e) (entry_claim e) env) else
        None
  end.

Lemma bit_run_sound : forall who goalb goal,
  (forall b, goalb b = true -> goal b) -> forall entries env result,
  trie_all (valid_claim who goal) env ->
    bit_run who goalb entries env = Some result ->
  trie_all (valid_claim who goal) result.
Proof.
  intros who goalb goal Hgoal entries. induction entries as [|e rest IH];
    intros env result Henv H.
  - simpl in H. inversion H; subst. exact Henv.
  - simpl in H. destruct (bit_node _ _ _ _ _) eqn:E; [|discriminate].
    eapply IH; [|exact H]. apply insert_all; [exact Henv|].
    eapply bit_node_sound; eauto.
Qed.

Definition bit_verify who goalb entries root b p :=
  match bit_run who goalb entries Tip with
  | None => false | Some env => reference env b p root end.

Theorem bit_verify_sound : forall who goalb goal,
  (forall b, goalb b = true -> goal b) -> forall entries root b p,
  bit_verify who goalb entries root b p = true -> forces who goal b p.
Proof.
  intros who goalb goal Hgoal entries root b p H. unfold bit_verify in H.
  destruct (bit_run who goalb entries Tip) as [env|] eqn:E; [|discriminate].
  eapply reference_sound; [|exact H]. eapply bit_run_sound; eauto. exact I.
Qed.
Print Assumptions bit_verify_sound.
