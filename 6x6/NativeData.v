From Stdlib Require Import List NArith.
From TPP2026.Six Require Import Rules Dag CutDag ImportDag TacticData.
From Ltac2 Require Import Ltac2 Array.
Declare ML Module "tpp_data".

Ltac2 @ external native_decode : int -> string -> constr array ->
  constr array -> constr array -> constr array -> constr := "tpp_data" "decode".
Ltac2 pose_native_certificate name count data :=
  let refs := Array.of_list [
    constr:(N0); constr:(Npos); constr:(Black); constr:(White);
    constr:(DEnd); constr:(DChoose); constr:(DAll); constr:(DPass);
    constr:(Claim); constr:(Entry); constr:(Regular);
    constr:(@cons positive); constr:(@nil positive);
    constr:(@cons cut_entry); constr:(@nil cut_entry);
    constr:(@cons (list cut_entry)); constr:(@nil (list cut_entry));
    constr:(@List.concat cut_entry)] in
  let entries := native_decode count data (byte_functions ()) (small_positives
    ()) (small_naturals ()) refs in
  Std.pose (Some name) entries.

Ltac2 @ external native_imports : string -> constr array -> constr array ->
  constr array -> constr array -> constr := "tpp_data" "imports".
Ltac2 pose_native_imports name data envs :=
  let refs := Array.of_list [constr:(@cons positive); constr:(@nil positive);
    constr:(Source); constr:(@cons import_source);
      constr:(@nil import_source)] in
  let sources := native_imports data (Array.of_list envs) (byte_functions ())
    (small_positives ()) refs in
  Std.pose (Some name) sources.

Ltac2 @ external native_trie : string -> constr array -> constr array ->
  constr array -> constr := "tpp_data" "trie".
Ltac2 refine_native_trie data :=
  let refs := Array.of_list [constr:(Claim); constr:(Black); constr:(White);
    constr:(N0); constr:(Npos); constr:(@Tip claim); constr:(@Branch claim);
    constr:(@None claim); constr:(@Some claim)] in
  let tree := native_trie data (byte_functions ()) (small_positives ()) refs in
  Control.refine (fun () => tree).

Ltac2 refine_native_ids data :=
  let refs := Array.of_list [constr:(@cons positive); constr:(@nil positive);
    constr:(Source); constr:(@cons import_source);
      constr:(@nil import_source)] in
  let sources := native_imports data (Array.of_list [constr:(@Tip claim)])
    (byte_functions ()) (small_positives ()) refs in
  let (_, args) := Constr.decompose_app sources in
  let head := Array.get args 1 in
  let (_, fields) := Constr.decompose_app head in
  let ids := Array.get fields 0 in
  Control.refine (fun () => ids).
