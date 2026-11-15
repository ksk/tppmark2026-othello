From Stdlib Require Import List.
From TPP2026.Six Require Import Dag ImportDag.
From TPP2026.Six.ExportExp Require Import ExportDag.

Lemma import_sources_checked : forall P sources imports,
  Forall (fun s => trie_all P (source_env s)) sources ->
  claim_trie_eqb (import_sources sources Tip) imports = true ->
  trie_all P imports.
Proof.
  intros P sources imports Hs He. apply claim_trie_eqb_sound in He.
  rewrite <- He. apply import_sources_sound; [exact Hs|exact I].
Qed.
Print Assumptions import_sources_checked.
