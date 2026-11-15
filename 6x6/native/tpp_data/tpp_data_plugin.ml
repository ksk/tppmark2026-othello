(* Untrusted data-to-syntax conversion. This module only constructs ordinary
   terms from supplied constructor references. It cannot assert a strategy,
   alter the kernel, or submit an unchecked proof. Qed checks every result. *)
open Ltac2_plugin
open Tac2ffi
open Tac2externals

let decode count data bytes small naturals refs =
  if Sys.int_size < 63 || count < 0 || Array.length bytes <> 256
     || Array.length small <> 256 || Array.length naturals <> 64
     || Array.length refs <> 18 then invalid_arg "tpp_data arguments";
  let app f args = EConstr.mkApp (f,Array.of_list args) in
  let apply i args = app refs.(i) args in
  let rec pos n =
    if n <= 0 then invalid_arg "nonpositive reference"
    else if n < 256 then small.(n)
    else app bytes.(n land 255) [pos (n lsr 8)] in
  let number n = if n=0 then refs.(0) else apply 1 [pos n] in
  let at=ref 0 in
  let read length =
    if !at+length > String.length data then invalid_arg "short certificate";
    let n=ref 0 in
    for j=0 to length-1 do
      let c=data.[!at+j] in
      let d=if c>='0' && c<='9' then Char.code c-48
        else if c>='a' && c<='f' then Char.code c-87
        else invalid_arg "invalid certificate hex" in
      n := (!n lsl 4) lor d
    done;
    at := !at+length; !n in
  let list cons nil xs = List.fold_right (fun x tail -> app cons [x;tail]) xs nil in
  let row () =
    let id=read 8 in let b=read 9 in let w=read 9 in
    let turn=read 1 in let action=read 2 in let nc=read 2 in
    if turn>1 || nc>36 then invalid_arg "invalid certificate row";
    let children=List.init nc (fun _ -> pos (read 8)) in
    let op=match action,children with
      | 0,[] -> refs.(4)
      | 37,_::_ -> apply 6 [list refs.(11) refs.(12) children]
      | 38,[c] -> apply 7 [c]
      | n,[c] when 1<=n && n<=36 -> apply 5 [naturals.(n-1);c]
      | _ -> invalid_arg "invalid instruction" in
    apply 10 [apply 9 [pos id;apply 8 [number b;number w;refs.(2+turn)];op]] in
  let rec chunks left acc =
    if left=0 then List.rev acc else
    let n=min left 64 in
    let entries=List.init n (fun _ -> row ()) in
    chunks (left-n) (list refs.(13) refs.(14) entries::acc) in
  let groups=chunks count [] in
  if !at<>String.length data then invalid_arg "trailing certificate data";
  apply 17 [list refs.(15) refs.(16) groups]

let () = define
  {Tac2expr.mltac_plugin="tpp_data";mltac_tactic="decode"}
  (int @-> string @-> array constr @-> array constr @-> array constr
    @-> array constr @-> ret constr) decode

let imports data envs bytes small refs =
  if Array.length bytes<>256 || Array.length small<>256 || Array.length refs<>5
  then invalid_arg "import arguments";
  let app f xs=EConstr.mkApp(f,Array.of_list xs) in
  let rec pos n=if n<=0 then invalid_arg "import id" else
    if n<256 then small.(n) else app bytes.(n land 255) [pos(n lsr 8)] in
  let at=ref 0 in
  let read ()=
    if !at+8>String.length data then invalid_arg "short imports";
    let n=ref 0 in
    for i=0 to 7 do
      let c=data.[!at+i] in
      let d=if c>='0'&&c<='9' then Char.code c-48 else if c>='a'&&c<='f' then Char.code c-87 else invalid_arg "import hex" in
      n:=(!n lsl 4) lor d
    done;at:= !at+8;!n in
  let sources=Array.to_list(Array.map(fun env ->
    let count=read () in
    if count>(String.length data- !at)/8 then invalid_arg "import count";
    let ids=List.init count(fun _ -> pos(read())) in
    let ids=List.fold_right(fun x t->app refs.(0)[x;t])ids refs.(1) in
    app refs.(2)[ids;env])envs) in
  if !at<>String.length data then invalid_arg "trailing imports";
  List.fold_right(fun x t->app refs.(3)[x;t])sources refs.(4)

let ()=define {Tac2expr.mltac_plugin="tpp_data";mltac_tactic="imports"}
  (string @-> array constr @-> array constr @-> array constr @-> array constr @-> ret constr) imports

type syntax_trie = Tip | Branch of syntax_trie * EConstr.t option * syntax_trie

let trie data bytes small refs =
  if Array.length bytes<>256 || Array.length small<>256 || Array.length refs<>9 then invalid_arg "trie arguments";
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
  let rec term=function Tip->refs.(5)|Branch(l,v,r)->
    let v=match v with None->refs.(7)|Some c->app refs.(8)[c] in
    app refs.(6)[term l;v;term r] in term !result

let ()=define {Tac2expr.mltac_plugin="tpp_data";mltac_tactic="trie"}
  (string @-> array constr @-> array constr @-> array constr @-> ret constr) trie
