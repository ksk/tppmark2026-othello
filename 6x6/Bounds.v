From Stdlib Require Import List Bool Arith ZArith.
From TPP2026.Six Require Import Rules.
Import ListNotations.

(** [protagonist] can force a terminal board satisfying [goal], regardless
    of every legal choice made by the other player. *)

Inductive forces (protagonist : player)
    (goal : board -> Prop) : board -> player -> Prop :=
| force_end : forall b p,
    terminal b -> goal b -> forces protagonist goal b p
| force_choose : forall b s b',
    legal_move b protagonist s b' ->
    forces protagonist goal b' (other protagonist) ->
    forces protagonist goal b protagonist
| force_all : forall b,
    has_move b (other protagonist) ->
    (forall s b', legal_move b (other protagonist) s b' ->
       forces protagonist goal b' protagonist) ->
    forces protagonist goal b (other protagonist)
| force_pass : forall b p,
    no_move b p -> has_move b (other p) ->
    forces protagonist goal b (other p) -> forces protagonist goal b p.

Scheme All for list.

Inductive certificate :=
| CEnd
| CChoose (square : nat) (next : certificate)
| CAll (replies : list certificate)
| CPass (next : certificate).

Fixpoint check_all {A B : Type} (f : A -> B -> bool) (xs : list A)
    (ys : list B) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => f x y && check_all f xs' ys'
  | _, _ => false
  end.

Fixpoint check (fuel : nat) (protagonist : player) (goal : board -> bool)
    (b : board) (p : player) (c : certificate) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
      match c with
      | CEnd => no_moveb b Black && no_moveb b White && goal b
      | CChoose s next =>
          if same_player p protagonist then
            match play b p s with
            | None => false
            | Some b' => check fuel' protagonist goal b' (other p) next
            end
          else false
      | CAll replies =>
          if same_player p (other protagonist) then
            match moves b p with
            | [] => false
            | ms => check_all
                      (fun mb child => check fuel' protagonist goal
                                         (snd mb) (other p) child)
                      ms replies
            end
          else false
      | CPass next => no_moveb b p && negb (no_moveb b (other p)) &&
                      check fuel' protagonist goal b (other p) next
      end
  end.

Lemma same_player_true : forall p q, same_player p q = true -> p = q.
Proof. destruct p, q; simpl; intros; congruence. Qed.

Lemma other_other : forall p, other (other p) = p.
Proof. destruct p; reflexivity. Qed.

Lemma check_all_member : forall (A B : Type) (f : A -> B -> bool) xs ys,
  check_all f xs ys = true ->
  forall x, In x xs -> exists y, f x y = true.
Proof.
  intros A B f xs. induction xs as [|a xs IH]; intros ys H x Hin.
  - contradiction.
  - destruct ys as [|y ys]; [discriminate|].
    simpl in H. apply andb_true_iff in H as [Hhead Htail].
    destruct Hin as [ <- |Hin].
    + exists y. exact Hhead.
    + eapply IH; eauto.
Qed.

Theorem check_sound : forall protagonist goalb goal,
  (forall b, goalb b = true -> goal b) ->
  forall fuel b p c,
  check fuel protagonist goalb b p c = true -> forces protagonist goal b p.
Proof.
  intros protagonist goalb goal Hgoal.
  induction fuel as [|fuel IH]; intros b p c H; [discriminate|].
  destruct c as [|s next|replies|next]; cbn [check] in H.
  - apply andb_true_iff in H as [Hmoves Hscore].
    apply andb_true_iff in Hmoves as [Hblack Hwhite].
    apply force_end.
    + split; apply no_moveb_spec; assumption.
    + apply Hgoal. exact Hscore.
  - destruct (same_player p protagonist) eqn:Hp; [|discriminate].
    apply same_player_true in Hp. subst p.
    destruct (play b protagonist s) as [b'|] eqn:Hplay; [|discriminate].
    eapply force_choose.
    + split; [eapply play_in_range; eauto|exact Hplay].
    + eapply IH. exact H.
  - destruct (same_player p (other protagonist)) eqn:Hp; [|discriminate].
    apply same_player_true in Hp. subst p. rewrite other_other in H.
    destruct (moves b (other protagonist)) as [|[s b'] rest] eqn:Hmoves;
      [discriminate|].
    apply force_all.
    + exists s, b'. apply moves_spec. rewrite Hmoves. simpl. auto.
    + intros t b'' Hlegal. apply moves_spec in Hlegal.
      rewrite Hmoves in Hlegal.
      destruct (check_all_member _ _ _ _ _ H (t, b'') Hlegal)
        as [child Hchild].
      eapply IH. exact Hchild.
  - apply andb_true_iff in H as [Hpass Hchild].
    apply andb_true_iff in Hpass as [Hnone Hsome].
    apply force_pass.
    + apply no_moveb_spec. exact Hnone.
    + apply has_moveb_spec. exact Hsome.
    + eapply IH. exact Hchild.
Qed.

Definition black_score (b : board) : Z :=
  (Z.of_nat (count b Black) - Z.of_nat (count b White))%Z.

Definition lower_bound (b : board) (turn : player) (z : Z) : Prop :=
  forces Black (fun terminal_board =>
    (z <= black_score terminal_board)%Z) b turn.

Definition upper_bound (b : board) (turn : player) (z : Z) : Prop :=
  forces White (fun terminal_board =>
    (black_score terminal_board <= z)%Z) b turn.

(** Both players can guarantee their respective bound.  This definition
    makes no assumption about a search result or a finite search depth. *)

Definition exact_score (b : board) (turn : player) (z : Z) : Prop :=
  lower_bound b turn z /\ upper_bound b turn z.

Corollary check_lower_sound : forall fuel b turn c z,
  check fuel Black (fun t => Z.leb z (black_score t)) b turn c = true ->
  lower_bound b turn z.
Proof.
  intros fuel b turn c z H.
  eapply check_sound; [|exact H]. intros t Ht. apply Z.leb_le. exact Ht.
Qed.

Corollary check_upper_sound : forall fuel b turn c z,
  check fuel White (fun t => Z.leb (black_score t) z) b turn c = true ->
  upper_bound b turn z.
Proof.
  intros fuel b turn c z H.
  eapply check_sound; [|exact H]. intros t Ht. apply Z.leb_le. exact Ht.
Qed.

Print Assumptions check_sound.
