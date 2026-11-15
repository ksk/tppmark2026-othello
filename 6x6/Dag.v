From Stdlib Require Import List Bool Arith NArith ZArith.
From TPP2026.Six Require Import Rules Bounds.
Import ListNotations.

(** Compact states are data, not assumptions. Every edge is checked against
    the existing list-board rules. Black takes priority on overlapping input
    bits; such data cannot bypass the rule or root-equality checks. *)

Record claim := Claim { black_bits : N; white_bits : N; claim_turn : player }.

Definition claim_board (c : claim) : board :=
  map (fun i => if N.testbit (black_bits c) (N.of_nat i) then Stone Black
                else if N.testbit (white_bits c) (N.of_nat i) then Stone White
                else Empty) squares.

Definition cell_eqb (x y : cell) : bool :=
  match x, y with
  | Empty, Empty => true
  | Stone p, Stone q => same_player p q
  | _, _ => false
  end.

Fixpoint board_eqb (b c : board) : bool :=
  match b, c with
  | [], [] => true
  | x :: xs, y :: ys => cell_eqb x y && board_eqb xs ys
  | _, _ => false
  end.

Lemma cell_eqb_sound : forall x y, cell_eqb x y = true -> x = y.
Proof. destruct x as [|p], y as [|q]; try discriminate; try reflexivity.
  simpl. intro H. apply same_player_true in H. now subst.
Qed.

Lemma board_eqb_sound : forall b c, board_eqb b c = true -> b = c.
Proof.
  induction b as [|x xs IH]; destruct c as [|y ys]; simpl; try discriminate;
    try reflexivity.
  intro H. apply andb_true_iff in H as [Hxy Htail].
  apply cell_eqb_sound in Hxy. apply IH in Htail. now subst.
Qed.

(** A binary trie indexed by positive numbers, with logarithmic lookup. *)

Inductive trie (A : Type) :=
  Tip | Branch (left : trie A) (value : option A) (right : trie A).
Arguments Tip {A}.
Arguments Branch {A} _ _ _.

Fixpoint lookup {A} (key : positive) (t : trie A) : option A :=
  match t with
  | Tip => None
  | Branch l v r => match key with xH => v | xO k => lookup k l | xI k =>
    lookup k r end
  end.

Fixpoint insert {A} (key : positive) (value : A) (t : trie A) : trie A :=
  let ' (l, v, r) := match t with Tip => (Tip, None, Tip) | Branch l v r =>
    (l, v, r) end in
  match key with
  | xH => Branch l (Some value) r
  | xO k => Branch (insert k value l) v r
  | xI k => Branch l v (insert k value r)
  end.

Fixpoint trie_all {A} (P : A -> Prop) (t : trie A) : Prop :=
  match t with
  | Tip => True
  | Branch l v r => trie_all P l /\ (forall a, v = Some a -> P a) /\
    trie_all P r
  end.

Lemma lookup_all : forall A (P : A -> Prop) t,
  trie_all P t -> forall key a, lookup key t = Some a -> P a.
Proof.
  intros A P t. induction t as [|l IHl v r IHr]; simpl.
  - intros _ key a H. destruct key; discriminate.
  - intros [Hl [Hv Hr]] key a H. destruct key; simpl in H; eauto.
Qed.

Lemma insert_all : forall A (P : A -> Prop) key value t,
  trie_all P t -> P value -> trie_all P (insert key value t).
Proof.
  intros A P key. induction key; intros value t Ht Hv; destruct t as [|l v r];
    simpl in *; repeat split; try tauto; try (intros a H; discriminate);
    try (intros a H; inversion H; subst; assumption); apply IHkey; tauto.
Qed.

Definition reference (env : trie claim) (b : board) (p : player)
    (id : positive) : bool :=
  match lookup id env with
  | None => false
  | Some c => board_eqb b (claim_board c) && same_player p (claim_turn c)
  end.

Definition valid_claim (who : player) (goal : board -> Prop)
    (c : claim) : Prop :=
  forces who goal (claim_board c) (claim_turn c).

Lemma reference_sound : forall who goal env,
  trie_all (valid_claim who goal) env ->
  forall b p id, reference env b p id = true -> forces who goal b p.
Proof.
  intros who goal env Henv b p id H.
  unfold reference in H. destruct (lookup id env) as [c|] eqn:Hget;
    [|discriminate].
  apply andb_true_iff in H as [Hb Hp].
  apply board_eqb_sound in Hb. apply same_player_true in Hp. subst b p.
  exact (lookup_all claim (valid_claim who goal) env Henv id c Hget).
Qed.

Inductive instruction :=
| DEnd
| DChoose (square : nat) (child : positive)
| DAll (children : list positive)
| DPass (child : positive).

Definition check_node (who : player) (goalb : board -> bool) (env : trie claim)
    (c : claim) (op : instruction) : bool :=
  let b := claim_board c in
  let p := claim_turn c in
  match op with
  | DEnd => no_moveb b Black && no_moveb b White && goalb b
  | DChoose square child =>
      if same_player p who then
        match play b who square with
        | None => false
        | Some b' => reference env b' (other who) child
        end
      else false
  | DAll children =>
      if same_player p (other who) then
        match moves b (other who) with
        | [] => false
        | ms => check_all (fun mb child =>
          reference env (snd mb) who child) ms children
        end
      else false
  | DPass child =>
    no_moveb b p && negb (no_moveb b (other p)) && reference env b (other p)
    child
  end.

Theorem check_node_sound : forall who goalb goal,
  (forall b, goalb b = true -> goal b) ->
  forall env c op, trie_all (valid_claim who goal) env ->
  check_node who goalb env c op = true -> valid_claim who goal c.
Proof.
  intros who goalb goal Hgoal env [bb wb p] op Henv H.
  unfold valid_claim. cbn [claim_turn].
  destruct op as [|s child|children|child]; cbn [check_node claim_turn] in H.
  - apply andb_true_iff in H as [Hmoves Hscore].
    apply andb_true_iff in Hmoves as [Hb Hw].
    apply force_end; [split; apply no_moveb_spec; assumption|auto].
  - destruct (same_player p who) eqn:Hp; [|discriminate].
    apply same_player_true in Hp. subst p.
    destruct (play _ who s) as [b'|] eqn:Hplay; [|discriminate].
    eapply force_choose.
    + split; [eapply play_in_range; eauto|exact Hplay].
    + eapply reference_sound; eauto.
  - destruct (same_player p (other who)) eqn:Hp; [|discriminate].
    apply same_player_true in Hp. subst p.
    destruct (moves _ (other who)) as [|[s b'] rest] eqn:Hmoves;
      [discriminate|].
    apply force_all.
    + exists s, b'. apply moves_spec. rewrite Hmoves. simpl. auto.
    + intros t b'' Hlegal. apply moves_spec in Hlegal. rewrite Hmoves in Hlegal.
      destruct (check_all_member _ _ _ _ _ H (t, b'') Hlegal) as [child Hchild].
      eapply reference_sound; eauto.
  - apply andb_true_iff in H as [Hpass Hchild].
    apply andb_true_iff in Hpass as [Hnone Hsome].
    apply force_pass.
    + apply no_moveb_spec. exact Hnone.
    + apply has_moveb_spec. exact Hsome.
    + eapply reference_sound; eauto.
Qed.

Record entry :=
  Entry { entry_id : positive; entry_claim : claim; entry_op : instruction }.

Fixpoint run (who : player) (goalb : board -> bool) (entries : list entry)
    (env : trie claim) : option (trie claim) :=
  match entries with
  | [] => Some env
  | e :: rest =>
      if check_node who goalb env (entry_claim e) (entry_op e)
      then run who goalb rest (insert (entry_id e) (entry_claim e) env)
      else None
  end.

Theorem run_sound : forall who goalb goal,
  (forall b, goalb b = true -> goal b) ->
  forall entries env result, trie_all (valid_claim who goal) env ->
  run who goalb entries env = Some result ->
    trie_all (valid_claim who goal) result.
Proof.
  intros who goalb goal Hgoal entries. induction entries as [|e rest IH];
    intros env result Henv Hrun.
  - simpl in Hrun. inversion Hrun; subst. assumption.
  - simpl in Hrun.
    destruct (check_node who goalb env (entry_claim e) (entry_op e)) eqn:Hcheck;
      [|discriminate].
    eapply IH; [|exact Hrun]. apply insert_all; [exact Henv|].
    eapply check_node_sound; eauto.
Qed.

Definition verify who goalb entries root b p : bool :=
  match run who goalb entries Tip with
  | None => false
  | Some env => reference env b p root
  end.

Theorem verify_sound : forall who goalb goal,
  (forall b, goalb b = true -> goal b) ->
  forall entries root b p, verify who goalb entries root b p = true ->
    forces who goal b p.
Proof.
  intros who goalb goal Hgoal entries root b p H.
  unfold verify in H. destruct (run who goalb entries Tip) as [env|] eqn:Hrun;
    [|discriminate].
  eapply reference_sound; [|exact H]. eapply run_sound; eauto. exact I.
Qed.

Corollary verify_lower_sound : forall entries root b p z,
  verify Black (fun t => Z.leb z (black_score t)) entries root b p = true ->
  lower_bound b p z.
Proof.
  intros entries root b p z H. eapply verify_sound; [|exact H].
  intros t Ht. apply Z.leb_le. exact Ht.
Qed.

Corollary verify_upper_sound : forall entries root b p z,
  verify White (fun t => Z.leb (black_score t) z) entries root b p = true ->
  upper_bound b p z.
Proof.
  intros entries root b p z H. eapply verify_sound; [|exact H].
  intros t Ht. apply Z.leb_le. exact Ht.
Qed.

Print Assumptions verify_sound.
