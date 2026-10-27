import Lean
open Lean (Json JsonNumber)


def Json.getStr! (obj : Json) : String :=
  match obj.getStr? with
  | Except.ok s => s
  | Except.error e =>
    panic! s!"unexpected JSON object: {e}"

def Json.getArr! (obj : Json) : Array Json :=
  match obj.getArr? with
  | Except.ok s => s
  | Except.error e =>
    panic! s!"unexpected JSON object: {e}"


def Json.getNat! (obj : Json) : Nat :=
  match obj.getNat? with
  | Except.ok s => s
  | Except.error e =>
    panic! s!"unexpected JSON object: {e}"

def Json.getInt! (obj : Json) : Int :=
  match obj.getInt? with
  | Except.ok s => s
  | Except.error e =>
    panic! s!"unexpected JSON object: {e}"

def Json.getBool! (obj : Json) : Bool :=
  match obj.getBool? with
  | Except.ok s => s
  | Except.error e =>
    panic! s!"unexpected JSON object: {e}"


def Json.getNum! (obj : Json) : JsonNumber :=
  match obj.getNum? with
  | Except.ok s => s
  | Except.error e =>
    panic! s!"unexpected JSON object: {e}"

