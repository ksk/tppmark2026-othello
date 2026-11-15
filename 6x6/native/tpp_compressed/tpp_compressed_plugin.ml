(* This untrusted syntax loader builds ordinary lazy-trie constructors. *)
open Ltac2_plugin
open Tac2ffi
open Tac2externals

type syntax_trie = Tip | Branch of syntax_trie * EConstr.t option * syntax_trie

let trie data bytes small refs =
  if Array.length bytes<>256 || Array.length small<>256 || Array.length refs<>11 then invalid_arg "trie arguments";
  let app f xs=EConstr.mkApp(f,Array.of_list xs) in
  let rec pos n=if n<=0 then invalid_arg "trie id" else
    if n<256 then small.(n) else app bytes.(n land 255)[pos(n lsr 8)] in
  let number n=if n=0 then refs.(3) else app refs.(4)[pos n] in
  let at=ref 0 in
  let read len=
    if !at+len>String.length data then invalid_arg "short trie";
    let n=ref 0 in
    for i=0 to len-1 do
      let c=data.[!at+i] in
      let d=if c>='0'&&c<='9' then Char.code c-48 else if c>='a'&&c<='f' then Char.code c-87 else invalid_arg "trie hex" in
      n:=(!n lsl 4) lor d
    done;at:= !at+len;!n in
  let rec insert id value tree=
    let l,v,r=match tree with Tip->Tip,None,Tip|Branch(l,v,r)->l,v,r in
    if id=1 then Branch(l,Some value,r)
    else if id land 1=0 then Branch(insert(id lsr 1)value l,v,r)
    else Branch(l,v,insert(id lsr 1)value r) in
  let result=ref Tip in
  while !at<String.length data do
    let id=read 8 in let b=read 9 in let w=read 9 in let turn=read 1 in
    if id=0 || turn>1 then invalid_arg "trie entry";
    let value=app refs.(0)[number b;number w;refs.(1+turn)] in
    result:=insert id value !result
  done;
  let rec sole=function
    | Branch(Tip,Some c,Tip) -> Some(1,c)
    | Branch(l,None,Tip) -> Option.map (fun(k,c)->(2*k,c)) (sole l)
    | Branch(Tip,None,r) -> Option.map (fun(k,c)->(2*k+1,c)) (sole r)
    | _ -> None in
  let rec term tree=match sole tree with
    | Some(k,c) -> app refs.(10)[pos k;c]
    | None -> match tree with Tip->refs.(5)|Branch(l,v,r)->
      let v=match v with None->refs.(7)|Some c->app refs.(8)[c] in
      let thunk t = EConstr.mkLambda (Context.make_annot Names.Anonymous (EConstr.ERelevance.make Sorts.Relevant), refs.(9), EConstr.Vars.lift 1 t) in
      app refs.(6)[thunk(term l);v;thunk(term r)] in term !result

let ()=define {Tac2expr.mltac_plugin="tpp_compressed";mltac_tactic="trie"}
  (string @-> array constr @-> array constr @-> array constr @-> ret constr) trie
