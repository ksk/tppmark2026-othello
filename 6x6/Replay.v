From Stdlib Require Import List Bool.
From TPP2026.Six Require Import Rules.
Import ListNotations.

Definition advance (b : board) (p : player)
    (action : option nat) : option (board * player) :=
  match action with
  | Some s => match play b p s with
              | Some b' => Some (b', other p)
              | None => None
              end
  | None => if no_moveb b p && negb (no_moveb b (other p))
            then Some (b, other p) else None
  end.

Fixpoint replay (b : board) (p : player)
    (actions : list (option nat)) : option (board * player) :=
  match actions with
  | [] => Some (b, p)
  | action :: rest =>
      match advance b p action with
      | None => None
      | Some (b', q) => replay b' q rest
      end
  end.

Inductive reaches : board -> player -> board -> player -> Prop :=
| reaches_refl : forall b p, reaches b p b p
| reaches_step : forall b p b' q b'' r,
    transition b p b' q -> reaches b' q b'' r -> reaches b p b'' r.

Lemma advance_sound : forall b p action b' q,
  advance b p action = Some (b', q) -> transition b p b' q.
Proof.
  intros b p [s|] b' q H; cbn [advance] in H.
  - destruct (play b p s) as [c|] eqn:Hplay; [|discriminate].
    inversion H; subst. eapply transition_move.
    split; [eapply play_in_range; eauto|exact Hplay].
  - destruct (no_moveb b p && negb (no_moveb b (other p))) eqn:Hp;
      [|discriminate].
    inversion H; subst. apply andb_true_iff in Hp as [Hnone Hsome].
    apply transition_pass.
    + apply no_moveb_spec. exact Hnone.
    + apply has_moveb_spec. exact Hsome.
Qed.

Theorem replay_sound : forall actions b p b' q,
  replay b p actions = Some (b', q) -> reaches b p b' q.
Proof.
  induction actions as [|action rest IH]; intros b p b' q H;
    cbn [replay] in H.
  - inversion H; subst. constructor.
  - destruct (advance b p action) as [[c r]|] eqn:Hadvance;
      [|discriminate].
    eapply reaches_step.
    + eapply advance_sound. exact Hadvance.
    + eapply IH. exact H.
Qed.

Theorem reaches_preserves_board : forall b p b' q,
  reaches b p b' q -> well_formed b -> well_formed b'.
Proof.
  intros b p b' q H. induction H; intros Hb; [exact Hb|].
  apply IHreaches. eapply transition_preserves_board; eauto.
Qed.
