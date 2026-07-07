import Mathlib.Analysis.Real.Hyperreal
open Lean

/-- `x → ∞` — x is infinite. -/
syntax (name := tendsToInf) term:26 " → " "∞" : term
macro_rules (kind := tendsToInf)
  | `($x → ∞) => `(ArchimedeanClass.mk $x < 0)

@[app_unexpander LT.lt]
def tendsToInf.unexpand : PrettyPrinter.Unexpander
  | `($_ $a $b) =>
    match a, b with
    | `(ArchimedeanClass.mk $x), `(0) =>
      `($x → ∞)
    | _, _ =>
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

/-- `x → 0` — x is infinitesimal. -/
syntax (name := tendsToZero) term:26 " → " num : term
macro_rules (kind := tendsToZero)
  | `($x → 0) => `(0 < ArchimedeanClass.mk $x)

@[app_unexpander LT.lt]
def tendsToZero.unexpand : PrettyPrinter.Unexpander
  | `($_ $a $b) =>
    match a, b with
    | `(0), `(ArchimedeanClass.mk $x) =>
      `($x → 0)
    | _, _ =>
      throw ()
  | _ =>
    throw ()

/-- `x → 0⁺` — x is a positive infinitesimal (`0⁺`). -/
syntax (name := tendsToZeroPos) term:26 " → " num "⁺" : term
macro_rules (kind := tendsToZeroPos)
  | `($x → 0⁺) => `(0 < $x ∧ 0 < ArchimedeanClass.mk $x)

/-- `x → 0⁻` — x is a negative infinitesimal (`0⁻`). -/
syntax (name := tendsToZeroNeg) term:26 " → " num "⁻" : term
macro_rules (kind := tendsToZeroNeg)
  | `($x → 0⁻) => `($x < 0 ∧ 0 < ArchimedeanClass.mk $x)

@[app_unexpander And]
def tendsToPosNeg.unexpand : PrettyPrinter.Unexpander
  | `($_ $a $b) =>
    match a with
    | `(0 < $x) =>
      match b with
      | `($y → ∞) =>
        if x.raw == y.raw then `($y → +∞) else throw ()
      | `($y → 0) =>
        if x.raw == y.raw then `($y → 0⁺) else throw ()
      | _ =>
        throw ()
    | `($x < $zero) =>
      match zero with
      | `(0) =>
        match b with
        | `($y → ∞) =>
          if x.raw == y.raw then `($y → -∞) else throw ()
        | `($y → 0) =>
          if x.raw == y.raw then `($y → 0⁻) else throw ()
        | _ =>
          throw ()
      | _ =>
        throw ()
    | _ =>
      throw ()
  | _ =>
    throw ()

export ArchimedeanClass (stdPart)
