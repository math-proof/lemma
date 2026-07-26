import Mathlib.Analysis.Real.Hyperreal
open Lean

/-- `x → ∞` — x is infinite. -/
syntax (name := tendsToInf) term:26 " → " "∞" : term
macro_rules (kind := tendsToInf)
  | `($x → ∞) => `(ArchimedeanClass.mk $x < 0)

/-- `x → 0` — x is infinitesimal. -/
syntax (name := tendsToZero) term:26 " → " num : term
macro_rules (kind := tendsToZero)
  | `($x → 0) => `(0 < ArchimedeanClass.mk $x)

private partial def isZeroSyntax? : Syntax → Bool
  | `(0) => true
  | `(OfNat.ofNat $_ 0 $_) => true
  | stx =>
    match stx with
    | .atom _ val => val == "0"
    | _ => false

private partial def archimedeanMkArg? : Syntax → Option Syntax
  | `(ArchimedeanClass.mk $x) => some x
  | `(@ArchimedeanClass.mk $_ $x) => some x
  | stx =>
    match stx with
    | .node _ `ArchimedeanClass.mk args =>
      if 0 < args.size then some args[args.size - 1]! else none
    | _ => none

@[app_unexpander LT.lt]
def tendsToLt.unexpand : PrettyPrinter.Unexpander
  | `($_ $a $b) =>
    if let some x := archimedeanMkArg? a then
      if isZeroSyntax? b then
        let x : TSyntax `term := ⟨x⟩
        `(($x → ∞))
      else
        throw ()
    else if isZeroSyntax? a then
      match archimedeanMkArg? b with
      | some x =>
        let x : TSyntax `term := ⟨x⟩
        `(($x → 0))
      | none => throw ()
    else
      throw ()
  | _ =>
    throw ()

/-- `x → +∞` — x is positive infinite. -/
syntax (name := tendsToPosInf) term:26 " → " "+∞" : term
macro_rules (kind := tendsToPosInf)
  | `($x → +∞) => `(0 < $x ∧ ArchimedeanClass.mk $x < 0)

/-- `x → -∞` — x is negative infinite. -/
syntax (name := tendsToNegInf) term:26 " → " "-∞" : term
macro_rules (kind := tendsToNegInf)
  | `($x → -∞) => `($x < 0 ∧ ArchimedeanClass.mk $x < 0)

/-- `x → 0⁺` — x is a positive infinitesimal (`0⁺`). -/
syntax (name := tendsToZeroPos) term:26 " → " num "⁺" : term
macro_rules (kind := tendsToZeroPos)
  | `($x → 0⁺) => `(0 < $x ∧ 0 < ArchimedeanClass.mk $x)

/-- `x → 0⁻` — x is a negative infinitesimal (`0⁻`). -/
syntax (name := tendsToZeroNeg) term:26 " → " num "⁻" : term
macro_rules (kind := tendsToZeroNeg)
  | `($x → 0⁻) => `($x < 0 ∧ 0 < ArchimedeanClass.mk $x)

private partial def unparenTerm? : Syntax → Syntax
  | `(term| ($t)) => t
  | stx => stx

private partial def asTendsToZero? : Syntax → Option Syntax
  | `($x → 0) => some x
  | stx =>
    match unparenTerm? stx with
    | `($x → 0) => some x
    | _ => none

private partial def asTendsToInf? : Syntax → Option Syntax
  | `($x → ∞) => some x
  | stx =>
    match unparenTerm? stx with
    | `($x → ∞) => some x
    | _ => none

@[app_unexpander And]
def tendsToPosNeg.unexpand : PrettyPrinter.Unexpander
  | `($_ $a $b) =>
    match a with
    | `(0 < $x) =>
      match asTendsToInf? b with
      | some y =>
        if x == y then
          let y : TSyntax `term := ⟨y⟩
          `($y → +∞)
        else
          throw ()
      | none =>
        match asTendsToZero? b with
        | some y =>
          if x == y then
            let y : TSyntax `term := ⟨y⟩
            `($y → 0⁺)
          else
            throw ()
        | none => throw ()
    | `($x < $zero) =>
      match zero with
      | `(0) =>
        match asTendsToInf? b with
        | some y =>
          if x == y then
            let y : TSyntax `term := ⟨y⟩
            `($y → -∞)
          else
            throw ()
        | none =>
          match asTendsToZero? b with
          | some y =>
            if x == y then
              let y : TSyntax `term := ⟨y⟩
              `($y → 0⁻)
            else
              throw ()
          | none => throw ()
      | _ =>
        throw ()
    | _ =>
      throw ()
  | _ =>
    throw ()

export ArchimedeanClass (stdPart)
