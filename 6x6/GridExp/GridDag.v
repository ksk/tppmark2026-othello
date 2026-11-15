From Stdlib Require Import List Bool.
From TPP2026.Six Require Import Rules Bounds Dag FastDecode BitDag CutDag
  Endgame.
From TPP2026.Six.GridExp Require Import GridRules.
Import ListNotations.

Definition grid_node who goalb (env : trie claim) c op :=
  let p := claim_turn c in
  match op with
  | DEnd =>
    grid_no_moveb c Black && grid_no_moveb c White && goalb (fast_claim_board c)
  | DChoose s child => if same_player p who then
      match grid_play c who s with None => false
      | Some d => bit_reference env d (other who) child end else false
  | DAll children => if same_player p (other who) then
      match grid_moves c (other who) with
      | [] => false
      | ms => check_all (fun mc child =>
        bit_reference env (snd mc) who child) ms children
      end else false
  | DPass child => grid_no_moveb c p && negb (grid_no_moveb c (other p)) &&
                  bit_reference env c (other p) child
  end.

Lemma grid_node_correct : forall who goalb env c op,
  grid_node who goalb env c op = bit_node who goalb env c op.
Proof.
  intros who goalb env c op. destruct op; cbn [grid_node bit_node];
    rewrite ?grid_no_moveb_correct, ?grid_play_correct, ?grid_moves_correct;
      reflexivity.
Qed.

Definition grid_cut_node who goalb env e :=
  match e with
  | Regular e => grid_node who goalb env (entry_claim e) (entry_op e)
  | Search _ c fuel => endgame fuel who goalb c (claim_turn c)
  end.

Fixpoint grid_cut_check who goalb entries (env : trie claim) : bool :=
  match entries with [] => true | e :: rest =>
    grid_cut_node who goalb env e && grid_cut_check who goalb rest (insert
      (cut_id e) (cut_claim e) env) end.

Lemma grid_cut_correct : forall who goalb entries env,
  grid_cut_check who goalb entries env = cut_check who goalb entries env.
Proof.
  intros who goalb entries. induction entries as [|e rest IH]; intro env; simpl;
    [reflexivity|].
  rewrite IH. destruct e; cbn [grid_cut_node cut_node];
    rewrite ?grid_node_correct; reflexivity.
Qed.

Theorem grid_cut_sound : forall who goalb goal,
  (forall b, goalb b = true -> goal b) -> forall entries env,
  trie_all (valid_claim who goal) env ->
    grid_cut_check who goalb entries env = true ->
  trie_all (valid_claim who goal) (cut_store entries env).
Proof.
  intros who goalb goal Hgoal entries env Henv H. rewrite grid_cut_correct in H.
  eapply cut_block_sound; eauto.
Qed.
Print Assumptions grid_cut_sound.
