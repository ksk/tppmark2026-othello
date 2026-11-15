From Stdlib Require Import List Bool Arith ZArith Lia.
From TPP2026.Common Require Import Rules.
From TPP2026.Common.Proofs Require Import RuleFacts.
Import ListNotations.

(** Finite strategies and optimal play, independent of the board size. *)
Module Make (P : Rules.Pieces) (D : Rules.Dimension).
Module RuleTheory := RuleFacts.Make P D.
Include RuleTheory.
Import P.

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

(** Every move in this finite play preserves the game's minimax score. *)

Fixpoint optimal_replay (z : Z) b p actions : Prop :=
  exact_score b p z /\ match actions with
  | [] => terminal b
  | action :: rest => match advance b p action with
      | Some (c, q) => optimal_replay z c q rest
      | None => False end
  end.

End Make.
