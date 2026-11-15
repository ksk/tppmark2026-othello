From Stdlib Require Import List Bool NArith.
From TPP2026.Six Require Import Rules Bounds Dag ProjectDag CutDag.
From TPP2026.Six.GridExp Require Import GridDag.

Definition claim_eqb c d :=
  N.eqb (black_bits c) (black_bits d) &&
  N.eqb (white_bits c) (white_bits d) &&
  same_player (claim_turn c) (claim_turn d).

Lemma claim_eqb_sound : forall c d, claim_eqb c d = true -> c = d.
Proof.
  intros [b w p] [b' w' p'] H. unfold claim_eqb in H; simpl in H.
  apply andb_true_iff in H as [H Hp]. apply andb_true_iff in H as [Hb Hw].
  apply N.eqb_eq in Hb. apply N.eqb_eq in Hw. apply same_player_true in Hp.
  now subst.
Qed.

Definition option_claim_eqb x y :=
  match x, y with
  | None, None => true
  | Some c, Some d => claim_eqb c d
  | _, _ => false
  end.

Lemma option_claim_eqb_sound : forall x y, option_claim_eqb x y = true -> x = y.
Proof.
  intros [c|] [d|]; simpl; try discriminate; try reflexivity.
  intro H. apply claim_eqb_sound in H. now subst.
Qed.

Fixpoint claim_trie_eqb (x y : trie claim) :=
  match x, y with
  | Tip, Tip => true
  | Branch l v r, Branch l' v' r' =>
      option_claim_eqb v v' && claim_trie_eqb l l' && claim_trie_eqb r r'
  | _, _ => false end.

Lemma claim_trie_eqb_sound : forall x y, claim_trie_eqb x y = true -> x = y.
Proof.
  induction x as [|l IHl v r IHr]; destruct y as [|l' v' r']; simpl;
    try discriminate; try reflexivity.
  intro H. apply andb_true_iff in H as [H Hr].
  apply andb_true_iff in H as [Hv Hl].
  apply option_claim_eqb_sound in Hv. apply IHl in Hl. apply IHr in Hr.
  now subst.
Qed.

(** Reflect interface equality as well as the game checks. This avoids
    reducing the complete stored trie by ordinary conversion at Qed. *)

Definition grid_export_check who goalb entries imports ids exports :=
  grid_cut_check who goalb entries imports &&
  claim_trie_eqb (project ids (cut_store entries imports)) exports.

Theorem grid_export_sound : forall who goalb goal,
  (forall b, goalb b = true -> goal b) -> forall entries imports ids exports,
  trie_all (valid_claim who goal) imports ->
  grid_export_check who goalb entries imports ids exports = true ->
  trie_all (valid_claim who goal) exports.
Proof.
  intros who goalb goal Hg entries imports ids exports Hi H.
  unfold grid_export_check in H. apply andb_true_iff in H as [Hc He].
  apply claim_trie_eqb_sound in He. rewrite <- He.
  apply project_sound. eapply grid_cut_sound; eauto.
Qed.
Print Assumptions grid_export_sound.
