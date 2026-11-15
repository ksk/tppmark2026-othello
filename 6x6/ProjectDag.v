From Stdlib Require Import List BinPos.
From TPP2026.Six Require Import Dag BlockDag.
Import ListNotations.

Fixpoint project {A} (ids : list positive) (env : trie A) : trie A :=
  match ids with
  | [] => Tip
  | id :: rest => let tail := project rest env in
      match lookup id env with None => tail | Some c => insert id c tail end
  end.

Lemma project_sound : forall A (P : A -> Prop) ids env,
  trie_all P env -> trie_all P (project ids env).
Proof.
  intros A P ids. induction ids as [|id rest IH]; intros env H; simpl;
    [exact I|].
  destruct (lookup id env) as [c|] eqn:E.
  - apply insert_all; [apply IH; exact H|]. eapply lookup_all; eauto.
  - apply IH; exact H.
Qed.
Print Assumptions project_sound.
