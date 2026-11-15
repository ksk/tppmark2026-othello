From Stdlib Require Import List Bool Arith Lia.
From TPP2026.Four Require Import Rules.
Import ListNotations.

(** An inductive, finite winning strategy.  Black may choose ANY legal
    move; White needs ONE legal winning reply.  Passing is compulsory
    precisely when the player cannot move and the opponent can. *)

Inductive white_wins : board -> player -> Prop :=
| win_terminal : forall b p,
    terminal b -> white_ahead b -> white_wins b p
| win_white_move : forall b s b',
    legal_move b White s b' -> white_wins b' Black -> white_wins b White
| win_black_moves : forall b,
    has_move b Black ->
    (forall s b', legal_move b Black s b' -> white_wins b' White) ->
    white_wins b Black
| win_pass : forall b p,
    no_move b p -> has_move b (other p) ->
    white_wins b (other p) -> white_wins b p.

(** Certificates are untrusted data.  Replies are in the exact order
    of [moves]; a missing or extra reply causes rejection. *)
Scheme All for list.

Inductive certificate :=
| CEnd
| CWhite (square : nat) (next : certificate)
| CBlack (replies : list certificate)
| CPass (next : certificate).

Fixpoint check_all {A B : Type} (f : A -> B -> bool) (xs : list A)
    (ys : list B) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => f x y && check_all f xs' ys'
  | _, _ => false
  end.

Fixpoint check (fuel : nat) (b : board) (p : player) (c : certificate) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
      match c with
      | CEnd => no_moveb b Black && no_moveb b White &&
                (count b Black <? count b White)
      | CWhite s next =>
          match p with
          | Black => false
          | White => match play b White s with
                     | None => false
                     | Some b' => check fuel' b' Black next
                     end
          end
      | CBlack replies =>
          match p with
          | White => false
          | Black =>
              match moves b Black with
              | [] => false
              | ms => check_all
                        (fun mb child => check fuel' (snd mb) White child)
                        ms replies
              end
          end
      | CPass next => no_moveb b p && negb (no_moveb b (other p)) &&
                      check fuel' b (other p) next
      end
  end.

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

(** Soundness holds for EVERY certificate and EVERY fuel value.
    In particular, running out of fuel can never prove a false win. *)

Theorem check_sound : forall fuel b p c,
  check fuel b p c = true -> white_wins b p.
Proof.
  induction fuel as [|fuel IH]; intros b p c H; [discriminate|].
  destruct c as [|s next|replies|next]; cbn [check] in H.
  - apply andb_true_iff in H as [Hmoves Hscore].
    apply andb_true_iff in Hmoves as [Hblack Hwhite].
    apply win_terminal.
    + split; apply no_moveb_spec; assumption.
    + apply Nat.ltb_lt. exact Hscore.
  - destruct p; [discriminate|].
    destruct (play b White s) as [b'|] eqn:Hplay; [|discriminate].
    eapply win_white_move.
    + split; [eapply play_in_range; eauto|exact Hplay].
    + eapply IH. exact H.
  - destruct p; [|discriminate].
    destruct (moves b Black) as [|[s b'] rest] eqn:Hmoves;
      [discriminate|].
    apply win_black_moves.
    + exists s, b'. apply moves_spec. rewrite Hmoves. simpl. auto.
    + intros t b'' Hlegal. apply moves_spec in Hlegal.
      rewrite Hmoves in Hlegal.
      destruct (check_all_member _ _ _ _ _ H (t, b'') Hlegal)
        as [child Hchild].
      eapply IH. exact Hchild.
  - apply andb_true_iff in H as [Hpass Hchild].
    apply andb_true_iff in Hpass as [Hnone Hsome].
    apply win_pass.
    + apply no_moveb_spec. exact Hnone.
    + apply has_moveb_spec. exact Hsome.
    + eapply IH. exact Hchild.
Qed.
