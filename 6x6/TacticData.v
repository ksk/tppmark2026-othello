From Stdlib Require Import List NArith.
From TPP2026.Six Require Import Rules Dag CutDag BinaryBytes.
From Ltac2 Require Import Ltac2 String Char Int Array.
(** Untrusted syntax generation only. This tactic constructs ordinary
    inductive data; all strategy facts are checked by the kernel. *)
Ltac2 byte_functions () := Array.of_list [constr:(w00); constr:(w01);
  constr:(w02); constr:(w03); constr:(w04); constr:(w05); constr:(w06);
  constr:(w07); constr:(w08); constr:(w09); constr:(w0a); constr:(w0b);
  constr:(w0c); constr:(w0d); constr:(w0e); constr:(w0f); constr:(w10);
  constr:(w11); constr:(w12); constr:(w13); constr:(w14); constr:(w15);
  constr:(w16); constr:(w17); constr:(w18); constr:(w19); constr:(w1a);
  constr:(w1b); constr:(w1c); constr:(w1d); constr:(w1e); constr:(w1f);
  constr:(w20); constr:(w21); constr:(w22); constr:(w23); constr:(w24);
  constr:(w25); constr:(w26); constr:(w27); constr:(w28); constr:(w29);
  constr:(w2a); constr:(w2b); constr:(w2c); constr:(w2d); constr:(w2e);
  constr:(w2f); constr:(w30); constr:(w31); constr:(w32); constr:(w33);
  constr:(w34); constr:(w35); constr:(w36); constr:(w37); constr:(w38);
  constr:(w39); constr:(w3a); constr:(w3b); constr:(w3c); constr:(w3d);
  constr:(w3e); constr:(w3f); constr:(w40); constr:(w41); constr:(w42);
  constr:(w43); constr:(w44); constr:(w45); constr:(w46); constr:(w47);
  constr:(w48); constr:(w49); constr:(w4a); constr:(w4b); constr:(w4c);
  constr:(w4d); constr:(w4e); constr:(w4f); constr:(w50); constr:(w51);
  constr:(w52); constr:(w53); constr:(w54); constr:(w55); constr:(w56);
  constr:(w57); constr:(w58); constr:(w59); constr:(w5a); constr:(w5b);
  constr:(w5c); constr:(w5d); constr:(w5e); constr:(w5f); constr:(w60);
  constr:(w61); constr:(w62); constr:(w63); constr:(w64); constr:(w65);
  constr:(w66); constr:(w67); constr:(w68); constr:(w69); constr:(w6a);
  constr:(w6b); constr:(w6c); constr:(w6d); constr:(w6e); constr:(w6f);
  constr:(w70); constr:(w71); constr:(w72); constr:(w73); constr:(w74);
  constr:(w75); constr:(w76); constr:(w77); constr:(w78); constr:(w79);
  constr:(w7a); constr:(w7b); constr:(w7c); constr:(w7d); constr:(w7e);
  constr:(w7f); constr:(w80); constr:(w81); constr:(w82); constr:(w83);
  constr:(w84); constr:(w85); constr:(w86); constr:(w87); constr:(w88);
  constr:(w89); constr:(w8a); constr:(w8b); constr:(w8c); constr:(w8d);
  constr:(w8e); constr:(w8f); constr:(w90); constr:(w91); constr:(w92);
  constr:(w93); constr:(w94); constr:(w95); constr:(w96); constr:(w97);
  constr:(w98); constr:(w99); constr:(w9a); constr:(w9b); constr:(w9c);
  constr:(w9d); constr:(w9e); constr:(w9f); constr:(wa0); constr:(wa1);
  constr:(wa2); constr:(wa3); constr:(wa4); constr:(wa5); constr:(wa6);
  constr:(wa7); constr:(wa8); constr:(wa9); constr:(waa); constr:(wab);
  constr:(wac); constr:(wad); constr:(wae); constr:(waf); constr:(wb0);
  constr:(wb1); constr:(wb2); constr:(wb3); constr:(wb4); constr:(wb5);
  constr:(wb6); constr:(wb7); constr:(wb8); constr:(wb9); constr:(wba);
  constr:(wbb); constr:(wbc); constr:(wbd); constr:(wbe); constr:(wbf);
  constr:(wc0); constr:(wc1); constr:(wc2); constr:(wc3); constr:(wc4);
  constr:(wc5); constr:(wc6); constr:(wc7); constr:(wc8); constr:(wc9);
  constr:(wca); constr:(wcb); constr:(wcc); constr:(wcd); constr:(wce);
  constr:(wcf); constr:(wd0); constr:(wd1); constr:(wd2); constr:(wd3);
  constr:(wd4); constr:(wd5); constr:(wd6); constr:(wd7); constr:(wd8);
  constr:(wd9); constr:(wda); constr:(wdb); constr:(wdc); constr:(wdd);
  constr:(wde); constr:(wdf); constr:(we0); constr:(we1); constr:(we2);
  constr:(we3); constr:(we4); constr:(we5); constr:(we6); constr:(we7);
  constr:(we8); constr:(we9); constr:(wea); constr:(web); constr:(wec);
  constr:(wed); constr:(wee); constr:(wef); constr:(wf0); constr:(wf1);
  constr:(wf2); constr:(wf3); constr:(wf4); constr:(wf5); constr:(wf6);
  constr:(wf7); constr:(wf8); constr:(wf9); constr:(wfa); constr:(wfb);
  constr:(wfc); constr:(wfd); constr:(wfe); constr:(wff)].
Ltac2 small_positives () := Array.of_list [constr:(1%positive);
  constr:(1%positive); constr:(2%positive); constr:(3%positive);
  constr:(4%positive); constr:(5%positive); constr:(6%positive);
  constr:(7%positive); constr:(8%positive); constr:(9%positive);
  constr:(10%positive); constr:(11%positive); constr:(12%positive);
  constr:(13%positive); constr:(14%positive); constr:(15%positive);
  constr:(16%positive); constr:(17%positive); constr:(18%positive);
  constr:(19%positive); constr:(20%positive); constr:(21%positive);
  constr:(22%positive); constr:(23%positive); constr:(24%positive);
  constr:(25%positive); constr:(26%positive); constr:(27%positive);
  constr:(28%positive); constr:(29%positive); constr:(30%positive);
  constr:(31%positive); constr:(32%positive); constr:(33%positive);
  constr:(34%positive); constr:(35%positive); constr:(36%positive);
  constr:(37%positive); constr:(38%positive); constr:(39%positive);
  constr:(40%positive); constr:(41%positive); constr:(42%positive);
  constr:(43%positive); constr:(44%positive); constr:(45%positive);
  constr:(46%positive); constr:(47%positive); constr:(48%positive);
  constr:(49%positive); constr:(50%positive); constr:(51%positive);
  constr:(52%positive); constr:(53%positive); constr:(54%positive);
  constr:(55%positive); constr:(56%positive); constr:(57%positive);
  constr:(58%positive); constr:(59%positive); constr:(60%positive);
  constr:(61%positive); constr:(62%positive); constr:(63%positive);
  constr:(64%positive); constr:(65%positive); constr:(66%positive);
  constr:(67%positive); constr:(68%positive); constr:(69%positive);
  constr:(70%positive); constr:(71%positive); constr:(72%positive);
  constr:(73%positive); constr:(74%positive); constr:(75%positive);
  constr:(76%positive); constr:(77%positive); constr:(78%positive);
  constr:(79%positive); constr:(80%positive); constr:(81%positive);
  constr:(82%positive); constr:(83%positive); constr:(84%positive);
  constr:(85%positive); constr:(86%positive); constr:(87%positive);
  constr:(88%positive); constr:(89%positive); constr:(90%positive);
  constr:(91%positive); constr:(92%positive); constr:(93%positive);
  constr:(94%positive); constr:(95%positive); constr:(96%positive);
  constr:(97%positive); constr:(98%positive); constr:(99%positive);
  constr:(100%positive); constr:(101%positive); constr:(102%positive);
  constr:(103%positive); constr:(104%positive); constr:(105%positive);
  constr:(106%positive); constr:(107%positive); constr:(108%positive);
  constr:(109%positive); constr:(110%positive); constr:(111%positive);
  constr:(112%positive); constr:(113%positive); constr:(114%positive);
  constr:(115%positive); constr:(116%positive); constr:(117%positive);
  constr:(118%positive); constr:(119%positive); constr:(120%positive);
  constr:(121%positive); constr:(122%positive); constr:(123%positive);
  constr:(124%positive); constr:(125%positive); constr:(126%positive);
  constr:(127%positive); constr:(128%positive); constr:(129%positive);
  constr:(130%positive); constr:(131%positive); constr:(132%positive);
  constr:(133%positive); constr:(134%positive); constr:(135%positive);
  constr:(136%positive); constr:(137%positive); constr:(138%positive);
  constr:(139%positive); constr:(140%positive); constr:(141%positive);
  constr:(142%positive); constr:(143%positive); constr:(144%positive);
  constr:(145%positive); constr:(146%positive); constr:(147%positive);
  constr:(148%positive); constr:(149%positive); constr:(150%positive);
  constr:(151%positive); constr:(152%positive); constr:(153%positive);
  constr:(154%positive); constr:(155%positive); constr:(156%positive);
  constr:(157%positive); constr:(158%positive); constr:(159%positive);
  constr:(160%positive); constr:(161%positive); constr:(162%positive);
  constr:(163%positive); constr:(164%positive); constr:(165%positive);
  constr:(166%positive); constr:(167%positive); constr:(168%positive);
  constr:(169%positive); constr:(170%positive); constr:(171%positive);
  constr:(172%positive); constr:(173%positive); constr:(174%positive);
  constr:(175%positive); constr:(176%positive); constr:(177%positive);
  constr:(178%positive); constr:(179%positive); constr:(180%positive);
  constr:(181%positive); constr:(182%positive); constr:(183%positive);
  constr:(184%positive); constr:(185%positive); constr:(186%positive);
  constr:(187%positive); constr:(188%positive); constr:(189%positive);
  constr:(190%positive); constr:(191%positive); constr:(192%positive);
  constr:(193%positive); constr:(194%positive); constr:(195%positive);
  constr:(196%positive); constr:(197%positive); constr:(198%positive);
  constr:(199%positive); constr:(200%positive); constr:(201%positive);
  constr:(202%positive); constr:(203%positive); constr:(204%positive);
  constr:(205%positive); constr:(206%positive); constr:(207%positive);
  constr:(208%positive); constr:(209%positive); constr:(210%positive);
  constr:(211%positive); constr:(212%positive); constr:(213%positive);
  constr:(214%positive); constr:(215%positive); constr:(216%positive);
  constr:(217%positive); constr:(218%positive); constr:(219%positive);
  constr:(220%positive); constr:(221%positive); constr:(222%positive);
  constr:(223%positive); constr:(224%positive); constr:(225%positive);
  constr:(226%positive); constr:(227%positive); constr:(228%positive);
  constr:(229%positive); constr:(230%positive); constr:(231%positive);
  constr:(232%positive); constr:(233%positive); constr:(234%positive);
  constr:(235%positive); constr:(236%positive); constr:(237%positive);
  constr:(238%positive); constr:(239%positive); constr:(240%positive);
  constr:(241%positive); constr:(242%positive); constr:(243%positive);
  constr:(244%positive); constr:(245%positive); constr:(246%positive);
  constr:(247%positive); constr:(248%positive); constr:(249%positive);
  constr:(250%positive); constr:(251%positive); constr:(252%positive);
  constr:(253%positive); constr:(254%positive); constr:(255%positive)].
Ltac2 small_naturals () := Array.of_list [constr:(0%nat); constr:(1%nat);
  constr:(2%nat); constr:(3%nat); constr:(4%nat); constr:(5%nat);
  constr:(6%nat); constr:(7%nat); constr:(8%nat); constr:(9%nat);
  constr:(10%nat); constr:(11%nat); constr:(12%nat); constr:(13%nat);
  constr:(14%nat); constr:(15%nat); constr:(16%nat); constr:(17%nat);
  constr:(18%nat); constr:(19%nat); constr:(20%nat); constr:(21%nat);
  constr:(22%nat); constr:(23%nat); constr:(24%nat); constr:(25%nat);
  constr:(26%nat); constr:(27%nat); constr:(28%nat); constr:(29%nat);
  constr:(30%nat); constr:(31%nat); constr:(32%nat); constr:(33%nat);
  constr:(34%nat); constr:(35%nat); constr:(36%nat); constr:(37%nat);
  constr:(38%nat); constr:(39%nat); constr:(40%nat); constr:(41%nat);
  constr:(42%nat); constr:(43%nat); constr:(44%nat); constr:(45%nat);
  constr:(46%nat); constr:(47%nat); constr:(48%nat); constr:(49%nat);
  constr:(50%nat); constr:(51%nat); constr:(52%nat); constr:(53%nat);
  constr:(54%nat); constr:(55%nat); constr:(56%nat); constr:(57%nat);
  constr:(58%nat); constr:(59%nat); constr:(60%nat); constr:(61%nat);
  constr:(62%nat); constr:(63%nat)].

(** Raw syntax construction is untrusted; Std.pose and Qed type-check it.
    No unchecked cast or unchecked proof submission is used. *)
Ltac2 syntax_app f args := Constr.Unsafe.make (Constr.Unsafe.App f
  (Array.of_list args)).
Ltac2 rec syntax_positive bytes small n :=
  if Int.lt n 256 then Array.get small n else
  let f := Array.get bytes (Int.mod n 256) in
  let tail := syntax_positive bytes small (Int.div n 256) in
  syntax_app f [tail].
Ltac2 syntax_N bytes small n :=
  if Int.equal n 0 then constr:(N0) else
  let p := syntax_positive bytes small n in syntax_app constr:(Npos) [p].
Ltac2 rec syntax_hex data pos fuel acc :=
  if Int.equal fuel 0 then (acc, pos) else
  let ch := Char.to_int (String.get data pos) in
  let digit := if Int.le ch 57 then Int.sub ch 48 else Int.sub ch 87 in
  if Bool.or (Int.lt digit 0) (Int.le 16 digit) then Control.throw
    (Invalid_argument None) else
  syntax_hex data (Int.add pos 1) (Int.sub fuel 1) (Int.add (Int.mul acc 16)
    digit).
Ltac2 rec syntax_children data pos fuel bytes small :=
  if Int.equal fuel 0 then (constr:(@nil positive), pos) else
  let (n, next) := syntax_hex data pos 8 0 in
  let head := syntax_positive bytes small n in
  let (tail, last) := syntax_children data next (Int.sub fuel 1) bytes small in
  (syntax_app constr:(@cons positive) [head; tail], last).
Ltac2 syntax_entry data pos bytes small naturals :=
  let (i, p1) := syntax_hex data pos 8 0 in
  let (b, p2) := syntax_hex data p1 9 0 in
  let (w, p3) := syntax_hex data p2 9 0 in
  let (t, p4) := syntax_hex data p3 1 0 in
  let (a, p5) := syntax_hex data p4 2 0 in
  let (n, p6) := syntax_hex data p5 2 0 in
  let (children, last) := syntax_children data p6 n bytes small in
  let id := syntax_positive bytes small i in
  let bb := syntax_N bytes small b in
  let wb := syntax_N bytes small w in
  let turn := if Int.equal t 0 then constr:(Black) else constr:(White) in
  let op := if Int.equal a 0 then constr:(DEnd) else
    if Int.equal a 37 then syntax_app constr:(DAll) [children] else
    let child := syntax_app constr:(@hd positive) [constr:(1%positive);
      children] in
    if Int.equal a 38 then syntax_app constr:(DPass) [child] else
    let square := Array.get naturals (Int.sub a 1) in syntax_app
      constr:(DChoose) [square; child] in
  (syntax_app constr:(Regular) [syntax_app constr:(Entry) [id;
    syntax_app constr:(Claim) [bb; wb; turn]; op]], last).
Ltac2 rec syntax_rows data pos fuel bytes small naturals :=
  if Int.equal fuel 0 then (constr:(@nil cut_entry), pos) else
  let (head, next) := syntax_entry data pos bytes small naturals in
  let (tail, last) := syntax_rows data next (Int.sub fuel 1) bytes small
    naturals in
  (syntax_app constr:(@cons cut_entry) [head; tail], last).
Ltac2 rec syntax_chunks data pos fuel bytes small naturals :=
  if Int.equal fuel 0 then constr:(@nil (list cut_entry)) else
  let count := if Int.lt fuel 64 then fuel else 64 in
  let (head, next) := syntax_rows data pos count bytes small naturals in
  let tail := syntax_chunks data next (Int.sub fuel count) bytes small naturals
    in
  syntax_app constr:(@cons (list cut_entry)) [head; tail].
Ltac2 pose_certificate name count data :=
  let rows := syntax_chunks data 0 count (byte_functions ()) (small_positives
    ()) (small_naturals ()) in
  let entries := syntax_app constr:(@List.concat cut_entry) [rows] in
  Std.pose (Some name) entries.
