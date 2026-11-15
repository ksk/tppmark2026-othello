From Stdlib Require Import List NArith.
From TPP2026.Six Require Import Rules Dag NativeData TacticData.
From TPP2026.Six.LinkExp Require Import CompressedLink.
From Ltac2 Require Import Ltac2 Array.
Declare ML Module "tpp_compressed".
Ltac2 @ external native_lazy_trie : string -> constr array -> constr array ->
  constr array -> constr := "tpp_compressed" "trie".
Ltac2 refine_lazy_trie data :=
  let refs := Array.of_list [constr:(Claim); constr:(Black); constr:(White);
    constr:(N0); constr:(Npos); constr:(LTip); constr:(LBranch);
    constr:(@None claim); constr:(@Some claim); constr:(unit);
      constr:(LLeaf)] in
  let tree := native_lazy_trie data (byte_functions ()) (small_positives ())
    refs in
  Control.refine (fun () => tree).
Ltac2 pose_lazy_imports name data envs :=
  let refs := Array.of_list [constr:(@cons positive); constr:(@nil positive);
    constr:(LazySource); constr:(@cons lazy_source);
      constr:(@nil lazy_source)] in
  let sources := native_imports data (Array.of_list envs) (byte_functions ())
    (small_positives ()) refs in
  Std.pose (Some name) sources.

Ltac2 pose_checked_imports name predicate data envs :=
  let refs := Array.of_list [constr:(@cons positive); constr:(@nil positive);
    constr:(make_checked_source $predicate);
    constr:(@cons (checked_source $predicate));
      constr:(@nil (checked_source $predicate))] in
  let sources := native_imports data (Array.of_list envs) (byte_functions ())
    (small_positives ()) refs in
  Std.pose (Some name) sources.
