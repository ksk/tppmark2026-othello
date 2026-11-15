From Ltac2 Require Import Ltac2.
Declare ML Module "tpp_audit".
Ltac2 @ external audit_closed : string -> unit := "tpp_audit" "audit".
Ltac2 @ external audit_closed_many : string list ->
  unit := "tpp_audit" "audit_many".
