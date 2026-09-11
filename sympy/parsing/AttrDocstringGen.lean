import Lean
import sympy.Basic
import stdlib.String
import stdlib.Lean.Name

open String Lean

def nameComponentString (n : Lean.Name) : String :=
  match n with
  | Lean.Name.str _ s => s
  | Lean.Name.num _ k => toString k
  | Lean.Name.anonymous => ""

def nameToModule (n : Lean.Name) : String :=
  String.intercalate "." (Lean.Name.components n |>.map nameComponentString)

def tokensFromRelPath (rel : String) : List String :=
  let s := (if rel.startsWith "Lemma/" then rel.drop 6 else rel).toString
  let s :=
    if s.endsWith ".lean" then
      (s.take (s.length - 5)).toString
    else
      s
  s.splitOn "/"

def moduleName (ts : List String) : String :=
  String.intercalate "." ts

/-- If the path already has `of`, append `Eq_n`; otherwise append `of.Eq_n`. -/
def substTokens (tokens : List String) (n : String) : List String :=
  if tokens.contains "of" then
    tokens ++ ["Eq_" ++ n]
  else
    tokens ++ ["of", "Eq_" ++ n]

def setAt (l : List String) (i : Nat) (x : String) : List String :=
  if _ : i < l.length then
    l.take i ++ [x] ++ l.drop (i + 1)
  else
    l

/-- `sh/run.sh` comm path transform (used for `@[comm n]` when `n > 0`). -/
partial def commRunSh (tokens : List String) (n : Nat) : List String :=
  if tokens.length > 2 && (tokens[2]! == "eq" || tokens[2]! == "is" || tokens[2]! == "as" ||
      tokens[2]! == "ne" || tokens[2]! == "lt" || tokens[2]! == "le" || tokens[2]! == "gt" ||
      tokens[2]! == "ge") then
    [tokens[0]!, tokens[3]!, tokens[2]!, tokens[1]!] ++ tokens.drop 4
  else
    let rec loop (toks : List String) (deBruijn : Nat) (index : Int) : List String :=
      if deBruijn == 0 then
        setAt toks 1 toks[1]!.transformPrefix
      else if deBruijn % 2 == 1 then
        let idx := Int.natAbs index
        loop (setAt toks idx toks[idx]!.transformPrefix) (deBruijn / 2) (index - 1)
      else
        loop toks (deBruijn / 2) (index - 1)
    loop tokens n (tokens.length - 1)

def parityBits (n : Nat) : List Bool :=
  (List.range (Nat.log2 n + 1)).map fun i => (n >>> i) % 2 == 1

def escapeMd (s : String) : String := s

def customAttrHead (attr : String) : String :=
  let parts := attr.trimAscii.toString.splitOn " " |>.filter (· != "")
  match parts with
  | ["mp", "and"] => "mp and"
  | ["mpr", "and"] => "mpr and"
  | ["mp.comm", "and"] => "mp.comm and"
  | ["mpr.comm", "and"] => "mpr.comm and"
  | h :: _ => h
  | _ => ""

def customAttrHeads : List String :=
  ["main", "comm", "mp", "mpr", "mp.comm", "mpr.comm", "comm.is", "is.comm", "mt", "mp.mt", "mpr.mt",
   "left", "right", "mpr.left", "mpr.right", "fin", "fin.comm", "fin.mp", "fin.mpr",
   "val", "subst", "cast", "cast.fin", "cast.comm", "mp and", "mpr and", "mp.comm and", "mpr.comm and"]

def isCustomAttr (attr : String) : Bool :=
  customAttrHead attr ∈ customAttrHeads

/-- Path-based parity for `of/...` segments when binder parity is unavailable. -/
def ofParityFromTokens (tokens : List String) : List Bool :=
  match tokens.idxOf? "of" with
  | some i =>
    let rest := tokens.drop (i + 1)
    (List.range rest.length).map fun _ => false
  | none => []

def simpleIsMpComm (tokens : List String) : Option (List String) :=
  if tokens.length >= 4 && tokens[2]! == "is" then
    match tokens.idxOf? "of" with
    | some i =>
      let beforeOf := tokens.take i
      let ofRest := tokens.drop (i + 1)
      if beforeOf.length >= 4 then
        some ([beforeOf[0]!, beforeOf[3]!.transformPrefix, "of", beforeOf[1]!.transformPrefix] ++ ofRest)
      else
        none
    | none =>
      some [tokens[0]!, tokens[3]!.transformPrefix, "of", tokens[1]!.transformPrefix]
  else
    none

def simpleIsMprComm (tokens : List String) : Option (List String) :=
  if tokens.length >= 4 && tokens[2]! == "is" then
    match tokens.idxOf? "of" with
    | some i =>
      let beforeOf := tokens.take i
      let ofRest := tokens.drop (i + 1)
      if beforeOf.length >= 4 then
        some ([beforeOf[0]!, beforeOf[1]!.transformPrefix, "of", beforeOf[3]!.transformPrefix] ++ ofRest)
      else
        none
    | none =>
      some [tokens[0]!, tokens[1]!.transformPrefix, "of", tokens[3]!.transformPrefix]
  else
    none

def mpCommLemmaTokens (tokens : List String) (parity : List Bool) : List String :=
  match simpleIsMpComm tokens with
  | some ts => ts
  | none => List.comm (List.mp tokens) parity

def mprCommLemmaTokens (tokens : List String) (parity : List Bool) : List String :=
  match simpleIsMprComm tokens with
  | some ts => ts
  | none => List.comm (List.mpr tokens) parity

/-- Build the full module `Name` from the post-`Lemma/` tokens. -/
def fullModuleName (tokens : List String) : Name :=
  tokens.foldl Name.str `Lemma

/-- Run a `CoreM` action in `IO` with a given environment. -/
def runCore {α : Type} (env : Environment) (act : CoreM α) : IO α := do
  let ctx : Core.Context := { fileName := "<gen>", fileMap := .ofString "" }
  let st : Core.State := { env }
  (·.1) <$> act.toIO ctx st

/-- Find the private `main` declaration of a module in the environment.
    `private lemma main ...` is stored as `_private.<Module>.<num>.main`. -/
def findPrivateMain (env : Environment) (moduleDotted : String) : Option ConstantInfo :=
  let pre := "_private." ++ moduleDotted ++ "."
  env.constants.fold (fun acc n c =>
    if acc.isSome then acc
    else if n.toString.startsWith pre && n.toString.endsWith ".main" then some c else acc) none

/-- Compute the exact `@[comm n]` generated name by replicating the real attribute
    handler (`Expr.comm` → `extractParity` → `List.comm`). The module must already
    be built so its private declarations are importable. -/
def exactCommName (env : Environment) (tokens : List String) (n : Nat) : CoreM (Option Name) := do
  let some info := findPrivateMain env (String.intercalate "." ("Lemma" :: tokens)) | return none
  let ⟨parity, _, _⟩ := Expr.comm info.type (.const info.name (info.levelParams.map .param)) n
  let i := tokens.idxOf "of"
  let ofPart := (tokens.splitAt i).snd.tail
  let parity ←
    if parity.length > ofPart.length && ofPart.length > 0 then
      parity.filterMapM fun ⟨comm, type⟩ =>
        try if ← Meta.MetaM.run' type.is_Prop then return some comm else return none
        catch _ => return none
    else
      pure (parity.map Prod.fst)
  let path := (tokens.comm parity).foldl Name.str default
  return path.lemmaName info.name

def attrLemmaName (tokens : List String) (attr : String) : String :=
  let parts := attr.trimAscii.toString.splitOn " " |>.filter (· != "")
  match parts with
  | ["main"] => moduleName tokens
  | ["comm"] => moduleName (List.comm tokens (ofParityFromTokens tokens))
  | ["comm", n] => moduleName (commRunSh tokens n.toNat!)
  | ["mp"] => moduleName (List.mp tokens)
  | ["mp", "and"] => moduleName (List.mp tokens)
  | ["mp", _] => moduleName (List.mp tokens)
  | ["mpr"] => moduleName (List.mpr tokens)
  | ["mpr", "and"] => moduleName (List.mpr tokens)
  | ["mpr", _] => moduleName (List.mpr tokens)
  | ["mp.comm"] => moduleName (mpCommLemmaTokens tokens (ofParityFromTokens tokens))
  | ["mp.comm", "and"] => moduleName (mpCommLemmaTokens tokens (ofParityFromTokens tokens))
  | ["mp.comm", _] => moduleName (mpCommLemmaTokens tokens (parityBits parts[1]!.toNat!))
  | ["mpr.comm"] => moduleName (mprCommLemmaTokens tokens (ofParityFromTokens tokens))
  | ["mpr.comm", "and"] => moduleName (mprCommLemmaTokens tokens (ofParityFromTokens tokens))
  | ["mpr.comm", _] => moduleName (mprCommLemmaTokens tokens (parityBits parts[1]!.toNat!))
  | ["comm.is"] => moduleName (List.comm.is tokens [])
  | ["comm.is", n] => moduleName (List.comm.is tokens (parityBits n.toNat!))
  | ["is.comm"] => moduleName (List.is.comm tokens [])
  | ["is.comm", n] => moduleName (List.is.comm tokens (parityBits n.toNat!))
  | ["fin"] => moduleName (tokens ++ ["fin"])
  | ["fin", _] => moduleName (tokens ++ ["fin"])
  | ["fin.comm"] => moduleName (List.comm tokens [] ++ ["fin"])
  | ["fin.mp"] => moduleName (List.mp tokens ++ ["fin"])
  | ["fin.mpr"] => moduleName (List.mpr tokens ++ ["fin"])
  | ["cast"] => moduleName (List.castPath tokens true)
  | ["cast", "false"] => moduleName (List.castPath tokens false)
  | ["cast.fin"] => moduleName (List.castPath tokens true ++ ["fin"])
  | ["cast", "fin"] => moduleName (List.castPath tokens true ++ ["fin"])
  | ["cast.comm"] => moduleName (List.comm (List.castPath tokens true) (ofParityFromTokens tokens))
  | ["cast.comm", n] => moduleName (List.comm (List.castPath tokens true) (parityBits n.toNat!))
  | ["left"] => nameToModule (tokens.left : Lean.Name)
  | ["right"] => nameToModule (tokens.right : Lean.Name)
  | ["mpr.left"] => nameToModule ((List.mpr tokens).left : Lean.Name)
  | ["mpr.right"] => nameToModule ((List.mpr tokens).right : Lean.Name)
  | ["val"] => moduleName (tokens ++ ["val"])
  | ["mt"] => nameToModule (List.mt tokens : Lean.Name)
  | ["mt", n] => nameToModule (List.mt tokens false n.toNat! : Lean.Name)
  | ["mp.mt"] => nameToModule (List.mt (List.mp tokens) : Lean.Name)
  | ["mp.mt", n] => nameToModule (List.mt (List.mp tokens) false n.toNat! : Lean.Name)
  | ["mpr.mt"] => nameToModule (List.mt (List.mpr tokens) : Lean.Name)
  | ["mpr.mt", n] => nameToModule (List.mt (List.mpr tokens) false n.toNat! : Lean.Name)
  | ["subst"] => moduleName (substTokens tokens "1")
  | ["subst", n] => moduleName (substTokens tokens n)
  | _ => panic! s!"unknown attribute: {attr}"

/-- Resolve the lemma name for an attribute. For `comm n`, uses the exact
    binder-aware engine algorithm by importing the built module; falls back to
    the token-only approximation if the module cannot be imported. -/
def attrLemmaNameIO (_rel : String) (tokens : List String) (attr : String) : IO String := do
  let parts := attr.trimAscii.toString.splitOn " " |>.filter (· != "")
  match parts with
  | ["comm", n] =>
    let modName := fullModuleName tokens
    try
      let env ← Lean.importModules #[{ module := modName }] {} 0
      let name? ← runCore env (exactCommName env tokens n.toNat!)
      match name? with
      | some name => return name.toString
      | none => return moduleName (commRunSh tokens n.toNat!)
    catch _ =>
      -- Module not built/importable (e.g. a failing lemma): use the token approximation.
      return moduleName (commRunSh tokens n.toNat!)
  | _ => return attrLemmaName tokens attr

def formatAttrLabel (attr : String) : String :=
  let parts := attr.trimAscii.toString.splitOn " " |>.filter (· != "")
  match parts with
  | ["mp", "and"] => "mp and"
  | ["mpr", "and"] => "mpr and"
  | ["mp.comm", "and"] => "mp.comm and"
  | ["mpr.comm", "and"] => "mpr.comm and"
  | _ => String.intercalate " " parts

def docstringFor (relPath : String) (attrs : List String) : IO String := do
  let tokens := tokensFromRelPath relPath
  let customAttrs := attrs.filter (· != "main") |>.filter isCustomAttr
  let rows ← ("main" :: customAttrs).mapM fun attr => do
    let label := formatAttrLabel attr
    let name ← attrLemmaNameIO relPath tokens attr
    pure s!"| {label} | {escapeMd name} |"
  return "/--\n| attributes | lemma |\n| :---: | :---: |\n" ++ String.intercalate "\n" rows ++ "\n-/"

def main (args : List String) : IO Unit := do
  match args with
  | ["--batch", path] =>
    let lines ← IO.FS.readFile path
    for rawLine in lines.splitOn "\n" do
      let line := rawLine.trimAscii.toString
      if line.isEmpty then
        pure ()
      else
        let parts := line.splitOn "|"
        let rel := parts.head!.trimAscii.toString
        let attrs := parts.tail.map (·.trimAscii.toString)
        IO.println s!"FILE:{rel}"
        IO.println (← docstringFor rel attrs)
        IO.println "---"
  | rel :: attrs =>
    IO.println (← docstringFor rel attrs)
  | _ =>
    IO.println "usage: AttrDocstringGen <Lemma/.../File.lean> <attr> ..."
    IO.println "       AttrDocstringGen --batch <lines.txt>"
