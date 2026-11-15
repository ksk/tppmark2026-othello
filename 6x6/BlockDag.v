From Stdlib Require Import List Bool.
From TPP2026.Six Require Import Rules Bounds Dag BitDag.
Import ListNotations.

Fixpoint store_entries (entries : list entry) (env : trie claim) : trie claim :=
  match entries with
  | [] => env
  | e :: rest => store_entries rest (insert (entry_id e) (entry_claim e) env)
  end.

Fixpoint check_block who goalb (entries : list entry)
    (env : trie claim) : bool :=
  match entries with
  | [] => true
  | e :: rest => bit_node who goalb env (entry_claim e) (entry_op e) &&
      check_block who goalb rest (insert (entry_id e) (entry_claim e) env)
  end.

Theorem block_sound : forall who goalb goal,
  (forall b, goalb b = true -> goal b) -> forall entries env,
  trie_all (valid_claim who goal) env ->
    check_block who goalb entries env = true ->
  trie_all (valid_claim who goal) (store_entries entries env).
Proof.
  intros who goalb goal Hgoal entries. induction entries as [|e rest IH];
    intros env Henv H.
  - exact Henv.
  - simpl in *. apply andb_true_iff in H as [He Hrest].
    apply IH; [|exact Hrest]. apply insert_all; [exact Henv|].
    eapply bit_node_sound; eauto.
Qed.

Lemma valid_some {A} {P : A -> Prop} {l r c} :
  trie_all P l -> P c -> trie_all P r -> trie_all P (Branch l (Some c) r).
Proof.
  simpl. intros Hl Hc Hr. repeat split; auto. intros a H. now inversion H;
    subst.
Qed.

Lemma valid_none {A} {P : A -> Prop} {l r} :
  trie_all P l -> trie_all P r -> trie_all P (Branch l None r).
Proof. simpl. intros Hl Hr. repeat split; auto. intros a H. discriminate. Qed.
Print Assumptions block_sound.
