import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Macro.Analysis.Real.Limits.Part8
open Lean
open scoped Topology


def isAtTopSyntax? : Syntax → Bool
  | `(Filter.atTop) | `(atTop) => true
  | _ => false

def isAtBotSyntax? : Syntax → Bool
  | `(Filter.atBot) | `(atBot) => true
  | _ => false

def reprintTrim (stx : Syntax) : String :=
  match (unparenTerm? stx).reprint with
  | some s => s
  | none => toString stx

def isNhdsWithinIdent? (stx : Syntax) : Bool :=
  stx.getId == `nhdsWithin

def limDirOfNhdsSet? (s : Syntax) : Option Nat :=
  let t := reprintTrim s
  if t.contains "Ioi" then some 1
  else if t.contains "Iio" then some 2
  else if t.contains "ᶜ" || t.contains "compl" then some 0
  else none

def asNhdsWithinArgs? (stx : Syntax) : Option (TSyntax `term × TSyntax `term) :=
  match unparenTerm? stx with
  | `($nw $x $s) =>
    if isNhdsWithinIdent? nw then some (x, s) else none
  | `($nw $_ $x $s) =>
    if isNhdsWithinIdent? nw then some (x, s) else none
  | `($nw $_ $_ $x $s) =>
    if isNhdsWithinIdent? nw then some (x, s) else none
  | _ => none

def isNhdsIdent? (stx : Syntax) : Bool :=
  stx.getId == `nhds

def asNhdsArg? (stx : Syntax) : Option (TSyntax `term) :=
  match unparenTerm? stx with
  | `($nh $a) =>
    if isNhdsIdent? nh then some a else none
  | `($nh $_ $a) =>
    if isNhdsIdent? nh then some a else none
  | `($nh $_ $_ $a) =>
    if isNhdsIdent? nh then some a else none
  | _ => none

/-- `0` / `x₀` as a `limPt` for `lim [x → x₀⁺]` / `lim [x → x₀⁻]`. -/
def asLimPt (x : Syntax) : PrettyPrinter.UnexpandM (TSyntax `limPt) := do
  match unparenTerm? x with
  | `($id:ident) => `(limPt| $id:ident)
  | `($z:num) => `(limPt| $z:num)
  | `(OfNat.ofNat $_ $z:num $_) => `(limPt| $z:num)
  | stx =>
    match stx with
    | .atom _ "0" => `(limPt| 0)
    | _ => throw ()

/-- Rebuild `lim [n → x₀] e`, `lim [n → x₀⁺] e`, … (`dir`: 0 two-sided, 1 right, 2 left). -/
def dummyLimBinder : TSyntax `ident := ⟨mkIdent `x⟩

def unexpandLimAt (n : TSyntax `ident) (x e : TSyntax `term) (dir : Nat)
    (ty? : Option (TSyntax `term) := none) (wild := false) (eq? : Option (TSyntax `term) := none) :
    PrettyPrinter.UnexpandM (TSyntax `term) := do
  match dir with
  | 0 =>
    match ty?, wild, eq? with
    | none, false, none => `(lim [$n:ident → $x:term] $e)
    | none, false, some a => `(lim [$n:ident → $x:term] $e = $a)
    | none, true, none => `(lim [_ → $x:term] $e)
    | none, true, some a => `(lim [_ → $x:term] $e = $a)
    | some ty, false, none => `(lim [($n:ident : $ty) → $x:term] $e)
    | some ty, false, some a => `(lim [($n:ident : $ty) → $x:term] $e = $a)
    | _, _, _ => throw ()
  | 1 =>
    let pt ← asLimPt x
    match ty?, wild, eq? with
    | none, false, none => `(lim [$n:ident → $pt:limPt⁺] $e)
    | none, false, some a => `(lim [$n:ident → $pt:limPt⁺] $e = $a)
    | none, true, none => `(lim [_ → $pt:limPt⁺] $e)
    | none, true, some a => `(lim [_ → $pt:limPt⁺] $e = $a)
    | some ty, false, none => `(lim [($n:ident : $ty) → $pt:limPt⁺] $e)
    | some ty, false, some a => `(lim [($n:ident : $ty) → $pt:limPt⁺] $e = $a)
    | _, _, _ => throw ()
  | 2 =>
    let pt ← asLimPt x
    match ty?, wild, eq? with
    | none, false, none => `(lim [$n:ident → $pt:limPt⁻] $e)
    | none, false, some a => `(lim [$n:ident → $pt:limPt⁻] $e = $a)
    | none, true, none => `(lim [_ → $pt:limPt⁻] $e)
    | none, true, some a => `(lim [_ → $pt:limPt⁻] $e = $a)
    | some ty, false, none => `(lim [($n:ident : $ty) → $pt:limPt⁻] $e)
    | some ty, false, some a => `(lim [($n:ident : $ty) → $pt:limPt⁻] $e = $a)
    | _, _, _ => throw ()
  | _ =>
    throw ()

/-- Infoview: print `Filter.limUnder … fun n ↦ e` as `lim [n → ∞] e`, `lim [x → 0] e`, … -/
@[app_unexpander Filter.limUnder]
def limUnder.unexpand : PrettyPrinter.Unexpander
  | `($_ $nw $x $s fun $n:ident => $e) =>
    if isNhdsWithinIdent? nw then
      match limDirOfNhdsSet? s with
      | some dir =>
        unexpandLimAt n x e dir
      | none => throw ()
    else
      throw ()
  | `($_ $nw $x $s fun ($n:ident : $ty) => $e) =>
    if isNhdsWithinIdent? nw then
      match limDirOfNhdsSet? s with
      | some dir =>
        unexpandLimAt n x e dir (ty? := some ty)
      | none => throw ()
    else
      throw ()
  | `($_ $nw $x $s fun _ => $e) =>
    if isNhdsWithinIdent? nw then
      match limDirOfNhdsSet? s with
      | some dir =>
        unexpandLimAt dummyLimBinder x e dir (wild := true)
      | none => throw ()
    else
      throw ()
  | `($_ $f fun $n:ident => $e) =>
    if isAtTopSyntax? f then
      `(lim [$n:ident → ∞] $e)
    else if isAtBotSyntax? f then
      `(lim [$n:ident → -∞] $e)
    else if let some (x, s) := asNhdsWithinArgs? f then
      match limDirOfNhdsSet? s with
      | some dir =>
        unexpandLimAt n x e dir
      | none => throw ()
    else
      throw ()
  | `($_ $f fun ($n:ident : $ty) => $e) =>
    if isAtTopSyntax? f then
      `(lim [($n:ident : $ty) → ∞] $e)
    else if isAtBotSyntax? f then
      `(lim [($n:ident : $ty) → -∞] $e)
    else if let some (x, s) := asNhdsWithinArgs? f then
      match limDirOfNhdsSet? s with
      | some dir =>
        unexpandLimAt n x e dir (ty? := some ty)
      | none => throw ()
    else
      throw ()
  | `($_ $f fun _ => $e) =>
    if isAtTopSyntax? f then
      `(lim [_ → ∞] $e)
    else if isAtBotSyntax? f then
      `(lim [_ → -∞] $e)
    else if let some (x, s) := asNhdsWithinArgs? f then
      match limDirOfNhdsSet? s with
      | some dir =>
        unexpandLimAt dummyLimBinder x e dir (wild := true)
      | none => throw ()
    else
      throw ()
  | _ =>
    throw ()

/-- Infoview: print `Tendsto (fun x => e) (𝓝[≠] x₀) (𝓝 a)` as `lim [x → x₀] e = a`. -/
@[app_unexpander Filter.Tendsto]
def tendstoLim.unexpand : PrettyPrinter.Unexpander
  | `($_ $f $l $na) =>
    if let some a := asNhdsArg? na then
      match f with
      | `(fun $n:ident => $e) =>
        if isAtTopSyntax? l then
          `(lim [$n:ident → ∞] $e = $a)
        else if isAtBotSyntax? l then
          `(lim [$n:ident → -∞] $e = $a)
        else if let some (x, s) := asNhdsWithinArgs? l then
          match limDirOfNhdsSet? s with
          | some dir =>
            unexpandLimAt n x e dir (eq? := some a)
          | none => throw ()
        else
          throw ()
      | `(fun ($n:ident : $ty) => $e) =>
        if isAtTopSyntax? l then
          `(lim [($n:ident : $ty) → ∞] $e = $a)
        else if isAtBotSyntax? l then
          `(lim [($n:ident : $ty) → -∞] $e = $a)
        else if let some (x, s) := asNhdsWithinArgs? l then
          match limDirOfNhdsSet? s with
          | some dir =>
            unexpandLimAt n x e dir (ty? := some ty) (eq? := some a)
          | none => throw ()
        else
          throw ()
      | `(fun _ => $e) =>
        if isAtTopSyntax? l then
          `(lim [_ → ∞] $e = $a)
        else if isAtBotSyntax? l then
          `(lim [_ → -∞] $e = $a)
        else if let some (x, s) := asNhdsWithinArgs? l then
          match limDirOfNhdsSet? s with
          | some dir =>
            unexpandLimAt dummyLimBinder x e dir (wild := true) (eq? := some a)
          | none => throw ()
        else
          throw ()
      | _ =>
        throw ()
    else
      throw ()
  | _ =>
    throw ()

