(* Read-only assumption audit. No proof terms or declarations are constructed.
   Rocq's own Assumptions traversal is used. After reading a large Bxxxxx
   proof, re-interning the same library resets its disk-proof cache; this
   prevents all certificate bodies from remaining resident simultaneously. *)
open Ltac2_plugin
open Tac2ffi
open Tac2externals

let block_library dp =
  let name=Names.DirPath.to_string dp in
  let prefix="TPP2026.Six." in
  let components=String.split_on_char '.' name in
  let base=List.hd(List.rev components) in
  String.starts_with ~prefix name && String.length base=6 && base.[0]='B' &&
  let good=ref true in
  for i=1 to 5 do if base.[i]<'0' || base.[i]>'9' then good:=false done; !good

let audit_many names =
  if names=[] then CErrors.user_err(Pp.str "No theorem was supplied for audit");
  let references=List.map (fun name -> Nametab.locate (Libnames.qualid_of_string name)) names in
  let normal=Library.indirect_accessor in
  let evicted=ref 0 in
  let access proof =
    let answer=normal.Global.access_proof proof in
    let (_,_,dp,_)=Opaqueproof.repr proof in
    if block_library dp then begin
      let file=match Loadpath.locate_absolute_library dp with
        | Ok file -> file | Error _ -> failwith "Cannot locate audited block" in
      (match fst (Library.intern_from_file file) with
       | Ok _ -> () | Error e -> Exninfo.iraise e);
      incr evicted;
      if !evicted mod 100=0 then
        Feedback.msg_notice(Pp.str(Printf.sprintf "Audited %d block proof bodies" !evicted))
    end;
    answer in
  let result=Assumptions.assumptions {Global.access_proof=access}
    TransparentState.full references in
  let env=Global.env() in
  Feedback.msg_notice(Printer.pr_assumptionset env (Evd.from_env env) result);
  if not(Printer.ContextObjectMap.is_empty result) || Environ.rewrite_rules_allowed env || Environ.is_impredicative_set env then
    CErrors.user_err(Pp.str "The audited theorem has assumptions")

let ()=define {Tac2expr.mltac_plugin="tpp_audit";mltac_tactic="audit"}
  (string @-> ret unit) (fun name -> audit_many [name])

let ()=define {Tac2expr.mltac_plugin="tpp_audit";mltac_tactic="audit_many"}
  (list string @-> ret unit) audit_many
