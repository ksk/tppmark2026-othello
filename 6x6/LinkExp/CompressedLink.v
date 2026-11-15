From Stdlib Require Import List BinPos.
From TPP2026.Six Require Import Dag.
From TPP2026.Six.ExportExp Require Import ExportDag.
Import ListNotations.

Inductive lazy_trie :=
  LTip
| LLeaf (key : positive) (value : claim)
| LBranch (left : unit -> lazy_trie) (value : option claim)
    (right : unit -> lazy_trie).

Fixpoint force_trie (t : lazy_trie) : trie claim :=
  match t with
  | LTip => Tip
  | LLeaf k c => insert k c Tip
  | LBranch l v r => Branch (force_trie (l tt)) v (force_trie (r tt))
  end.

Fixpoint lazy_lookup (key : positive) (t : lazy_trie) : option claim :=
  match t with
  | LTip => None
  | LLeaf k c => if Pos.eqb key k then Some c else None
  | LBranch l v r =>
      match key with xH => v
      | xO k => lazy_lookup k (l tt)
      | xI k => lazy_lookup k (r tt)
      end
  end.

Lemma lookup_singleton : forall key id (c : claim),
  lookup id (insert key c Tip) = if Pos.eqb id key then Some c else None.
Proof.
  induction key; intros id c; destruct id; simpl; auto; destruct id;
    reflexivity.
Qed.

Lemma lazy_lookup_correct : forall key t,
  lazy_lookup key t = lookup key (force_trie t).
Proof.
  intros key t. revert key. induction t as [|k c|l IHl v r IHr]; intro key.
  - destruct key; reflexivity.
  - pose proof (lookup_singleton k key c) as H. destruct key; simpl in *;
    symmetry; exact H.
  - destruct key; simpl; auto.
Qed.

Definition lazy_valid (P : claim -> Prop) t :=
  forall id c, lazy_lookup id t = Some c -> P c.

Lemma lazy_valid_lift : forall P t env,
  force_trie t = env -> trie_all P env -> lazy_valid P t.
Proof.
  intros P t env E H id c Hc. rewrite lazy_lookup_correct, E in Hc.
  exact (lookup_all claim P env H id c Hc).
Qed.

Record lazy_source :=
  LazySource { lazy_ids : list positive; lazy_env : lazy_trie }.

Fixpoint lazy_import_ids ids src (dst : trie claim) :=
  match ids with
  | [] => dst
  | id :: rest =>
      lazy_import_ids rest src
        (match lazy_lookup id src with None => dst
         | Some c => insert id c dst
         end)
  end.

Fixpoint lazy_import_sources sources dst :=
  match sources with
  | [] => dst
  | s :: rest =>
      lazy_import_sources rest (lazy_import_ids (lazy_ids s) (lazy_env s) dst)
  end.

Lemma lazy_import_ids_sound : forall P ids src dst,
  lazy_valid P src -> trie_all P dst ->
    trie_all P (lazy_import_ids ids src dst).
Proof.
  intros P ids. induction ids as [|id rest IH]; intros src dst Hs Hd; simpl;
    [exact Hd|].
  apply IH; [exact Hs|]. destruct (lazy_lookup id src) as [c|] eqn:E;
    [|exact Hd].
  apply insert_all; [exact Hd|exact (Hs id c E)].
Qed.

Lemma lazy_import_sources_sound : forall P sources dst,
  Forall (fun s => lazy_valid P (lazy_env s)) sources -> trie_all P dst ->
  trie_all P (lazy_import_sources sources dst).
Proof.
  intros P sources dst H. revert dst. induction H; intros dst Hd; simpl;
    [exact Hd|].
  apply IHForall. apply lazy_import_ids_sound; assumption.
Qed.
Print Assumptions lazy_valid_lift.
Print Assumptions lazy_import_sources_sound.

Lemma lazy_import_sources_checked : forall P sources imports,
  Forall (fun s => lazy_valid P (lazy_env s)) sources ->
  claim_trie_eqb (lazy_import_sources sources Tip) imports = true ->
  trie_all P imports.
Proof.
  intros P sources imports Hs He. apply claim_trie_eqb_sound in He.
  rewrite <- He. apply lazy_import_sources_sound; [exact Hs|exact I].
Qed.
Print Assumptions lazy_import_sources_checked.

(** Package validity with each input table. This avoids constructing a long
    explicit Forall proof separately at every block boundary. *)

Definition checked_environment P := { t : lazy_trie | lazy_valid P t }.

Definition checked_source P := { s : lazy_source | lazy_valid P (lazy_env s) }.

Definition make_checked_source P ids
    (env : checked_environment P) : checked_source P :=
  exist _ (LazySource ids (proj1_sig env)) (proj2_sig env).

Definition checked_import_sources P (sources : list (checked_source P)) dst :=
  lazy_import_sources
    (map (@proj1_sig lazy_source (fun s => lazy_valid P (lazy_env s))) sources)
    dst.

Lemma checked_sources_valid : forall P (sources : list (checked_source P)),
  Forall (fun s => lazy_valid P (lazy_env s))
    (map (@proj1_sig lazy_source (fun s => lazy_valid P (lazy_env s))) sources).
Proof.
  intros P sources. induction sources as [|[s Hs] rest IH]; simpl; constructor;
    assumption.
Qed.

Theorem checked_import_sources_checked : forall P sources imports,
  claim_trie_eqb (checked_import_sources P sources Tip) imports = true ->
  trie_all P imports.
Proof.
  intros P sources imports He. apply claim_trie_eqb_sound in He.
  rewrite <- He. unfold checked_import_sources. apply lazy_import_sources_sound.
  - apply checked_sources_valid.
  - exact I.
Qed.
Print Assumptions checked_import_sources_checked.
