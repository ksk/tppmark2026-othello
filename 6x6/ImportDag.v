From Stdlib Require Import List BinPos.
From TPP2026.Six Require Import Dag.
Import ListNotations.

Record import_source :=
  Source { source_ids : list positive; source_env : trie claim }.

Fixpoint import_ids ids (src dst : trie claim) :=
  match ids with
  | [] => dst
  | id :: rest =>
      import_ids rest src
        (match lookup id src with None => dst
         | Some c => insert id c dst
         end)
  end.

Fixpoint import_sources sources (dst : trie claim) :=
  match sources with
  | [] => dst
  | s :: rest =>
      import_sources rest (import_ids (source_ids s) (source_env s) dst)
  end.

Lemma import_ids_sound : forall (P : claim -> Prop) ids src dst,
  trie_all P src -> trie_all P dst -> trie_all P (import_ids ids src dst).
Proof.
  intros P ids. induction ids as [|id rest IH]; intros src dst Hsrc Hdst; simpl.
  - exact Hdst.
  - apply IH; [exact Hsrc|]. destruct (lookup id src) as [c|] eqn:E;
    [|exact Hdst].
    apply insert_all; [exact Hdst|]. exact (lookup_all claim P src Hsrc id c E).
Qed.

Theorem import_sources_sound : forall (P : claim -> Prop) sources dst,
  Forall (fun s => trie_all P (source_env s)) sources -> trie_all P dst ->
  trie_all P (import_sources sources dst).
Proof.
  intros P sources dst H. revert dst. induction H; intros dst Hd; simpl;
    [exact Hd|].
  apply IHForall. apply import_ids_sound; assumption.
Qed.
Print Assumptions import_sources_sound.
