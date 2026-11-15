From Stdlib Require Import List Bool Arith NArith.
From TPP2026.Six Require Import Rules Bounds Dag BitDag BlockDag Endgame.
Import ListNotations.

Inductive cut_entry :=
  Regular (e : entry) | Search (id : positive) (c : claim) (fuel : nat).

Definition cut_id e :=
  match e with Regular e => entry_id e | Search id _ _ => id end.

Definition cut_claim e :=
  match e with Regular e => entry_claim e | Search _ c _ => c end.

Definition cut_node who goalb env e :=
  match e with
  | Regular e => bit_node who goalb env (entry_claim e) (entry_op e)
  | Search _ c fuel => endgame fuel who goalb c (claim_turn c)
  end.

Fixpoint cut_store entries (env : trie claim) : trie claim :=
  match entries with [] => env
  | e :: rest => cut_store rest (insert (cut_id e) (cut_claim e) env)
  end.

Fixpoint cut_check who goalb entries (env : trie claim) : bool :=
  match entries with [] => true
  | e :: rest =>
      cut_node who goalb env e &&
      cut_check who goalb rest (insert (cut_id e) (cut_claim e) env)
  end.

Theorem cut_block_sound : forall who goalb goal,
  (forall b, goalb b = true -> goal b) -> forall entries env,
  trie_all (valid_claim who goal) env ->
    cut_check who goalb entries env = true ->
  trie_all (valid_claim who goal) (cut_store entries env).
Proof.
  intros who goalb goal Hgoal entries. induction entries as [|e rest IH];
    intros env Henv H.
  - exact Henv.
  - cbn [cut_check] in H. apply andb_true_iff in H as [He Hr].
    apply IH; [|exact Hr]. apply insert_all; [exact Henv|].
    destruct e as [e|id c fuel]; cbn [cut_node cut_claim] in *.
    + eapply bit_node_sound; eauto.
    + unfold valid_claim. eapply endgame_sound; eauto.
Qed.
Print Assumptions cut_block_sound.
