import Batteries.Data.String
import Lean.Meta
import Def.Lean.Char
import Macro.Data.String.String
open Lean.Meta
open Lean (Json JsonNumber)


def String.implode := String.intercalate

def String.replaceFirst (s : String) (old new : String) : String :=
  match s.findSubstr? old with
  | none => s
  | some ⟨_, startPos, stopPos⟩ =>
    let before : Substring.Raw := ⟨s, 0, startPos⟩
    let after : Substring.Raw := ⟨s, stopPos, s.rawEndPos⟩
    before.toString ++ new ++ after.toString


def String.escape_specials (s : String) : String :=
  -- extract the pattern from the string : ([a-zA-Z]+)_(.*)
  let ⟨head, tail⟩ := List.span (fun ch => ch.isAlpha || ch.isSubscriptDigit) s.toList
  if tail[0]? == some '_' then
    let tail := tail.drop 1
    let tail := String.ofList <| tail.flatMap fun c =>
      if c == '{' then ['\\', '{']
      else if c == '}' then ['\\', '}']
      else if c == '_' then ['\\', '_']
      else [c]
    let formatStr :=
      match head.length with
      | 0 => "%s\\_%s"
      | 1 => "{%s}_{%s}"
      | _ =>  "{%s}\\_%s"
    formatStr.printf [String.ofList head, tail]
  else s

def String.endsWithNumberedWord (s : String) (word : String) : Bool :=
  -- match the regexp expression : \\w+_\\d+
  if s.startsWith (word ++ "_") then
    let rest := s.drop (word.length + 1)
    !rest.isEmpty && rest.all Char.isDigit
  else
    false

def String.is_relational_operator : String → Bool
  | "et" | "ou" | "to" | "eq" | "ne" | "gt" | "lt" | "ge" | "le" | "in" | "as" | "dvd" | "subset" | "supset" => true
  | _ => false

partial def String.transformPrefix (s : String) : String :=
  match s.toList with
  | s₀ :: s₁ :: expr =>
    match s₀, s₁, expr with
    | 'E', 'q', s₂ :: expr
    | 'N', 'e', s₂ :: expr
    | 'O', 'r', s₂ :: expr =>
      String.ofList (s₀ :: s₁ :: s₂.transformExpr expr)
    | 'S', 'E', s₂@'q' :: s₃ :: expr
    | 'I', 'f', s₂@'f' :: s₃ :: expr
    | 'H', 'E', s₂@'q' :: s₃ :: expr
    | 'A', 'n', s₂@'d' :: s₃ :: expr =>
      String.ofList (s₀ :: s₁ :: s₂ :: s₃.transformExpr expr)
    | 'L', 't', _
    | 'L', 'e', _
    | 'G', 't', _
    | 'G', 'e', _ =>
      let s₀ := if s₀ == 'L' then 'G' else 'L'
      match expr with
      | s₂ :: expr =>
        String.ofList (s₀ :: s₁ :: s₂.transformExpr expr)
      | _ =>
        String.ofList [s₀, s₁]
    | 'N', 'o', 't' :: expr =>
      "Not" ++ (String.ofList expr).transformPrefix
    | 'A', 'l', 'l' :: '_' :: rest =>
      "All_" ++ (String.ofList rest).transformPrefix
    | _, _, _ =>
      s
  | _ =>
    s

def String.Not (s : String) : String :=
  if s.startsWith "Not" then
    (s.drop 3).toString
  else if s.startsWith "Eq" then
    "Ne" ++ (s.drop 2).toString
  else if s.startsWith "Ne" then
    "Eq" ++ (s.drop 2).toString
  else
    "Not" ++ s

-- #eval "%%Hello %%%-10s! %5.2f%%".format "World", -20.666666 + 1
-- #eval "number: %4.2f".format -1

