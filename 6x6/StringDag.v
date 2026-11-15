From Corelib Require Import PrimInt63 PrimString.
From Stdlib Require Import List NArith.
From TPP2026.Six Require Import Rules Dag.
Import ListNotations.

(** Primitive strings are only an input encoding. No arithmetic or string
    specification axiom is used: the decoded data pass the ordinary checker. *)

Fixpoint int_to_N (fuel : nat) (v : PrimInt63.int) : N :=
  if PrimInt63.eqb v 0 then 0%N
  else match fuel with
       | O => 0%N
       | S rest =>
           let tail := int_to_N rest (PrimInt63.lsr v 1) in
           if PrimInt63.eqb (PrimInt63.land v 1) 0 then N.double tail
           else N.succ_double tail
       end.

Definition hex_digit (c : PrimInt63.int) :=
  if PrimInt63.leb c 57 then PrimInt63.sub c 48 else PrimInt63.sub c 87.

Fixpoint read_hex (fuel : nat) (data : PrimString.string)
    (pos acc : PrimInt63.int) : PrimInt63.int * PrimInt63.int :=
  match fuel with
  | O => (acc, pos)
  | S rest => read_hex rest data (PrimInt63.add pos 1)
      (PrimInt63.add (PrimInt63.lsl acc 4)
        (hex_digit (PrimString.get data pos)))
  end.

Definition positive_of_int v :=
  match int_to_N 32 v with N0 => 1%positive | Npos p => p end.

Fixpoint string_children (fuel : nat) data pos
    : list positive * PrimInt63.int :=
  match fuel with
  | O => ([], pos)
  | S rest =>
      let ' (v, next) := read_hex 8 data pos 0 in
      let ' (children, finish) := string_children rest data next in
      (positive_of_int v :: children, finish)
  end.

Definition string_entry data pos : entry * PrimInt63.int :=
  let ' (id, p1) := read_hex 8 data pos 0 in
  let ' (bb, p2) := read_hex 9 data p1 0 in
  let ' (wb, p3) := read_hex 9 data p2 0 in
  let ' (turn, p4) := read_hex 1 data p3 0 in
  let ' (action, p5) := read_hex 2 data p4 0 in
  let ' (count, p6) := read_hex 2 data p5 0 in
  let ' (children, finish) :=
    string_children (N.to_nat (int_to_N 8 count)) data p6 in
  let op :=
    if PrimInt63.eqb action 0 then DEnd
    else if PrimInt63.eqb action 37 then DAll children
    else if PrimInt63.eqb action 38 then DPass (hd 1%positive children)
    else DChoose (Nat.pred (N.to_nat (int_to_N 8 action)))
           (hd 1%positive children)
  in
  (Entry (positive_of_int id)
     (Claim (int_to_N 36 bb) (int_to_N 36 wb)
       (if PrimInt63.eqb turn 0 then Black else White)) op,
   finish).

Fixpoint string_entries (fuel : nat) data pos : list entry :=
  match fuel with
  | O => []
  | S rest =>
      let ' (e, next) := string_entry data pos in
      e :: string_entries rest data next
  end.

Definition decode_string fuel data := string_entries fuel data 0.
