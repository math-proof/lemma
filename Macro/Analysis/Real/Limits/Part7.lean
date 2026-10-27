import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Def.Analysis.Real.Limits.Part2
open Lean
open scoped Topology


/-- `lim [n → ∞] e` — limit of `e` as `n` tends to `+∞` (`atTop`).
The type of `n` is inferred, or written `lim [(n : α) → ∞] e`.
Expands to `Filter.limUnder Filter.atTop fun n => e`. -/
macro:max (priority := 1003) "lim " "[" n:binderIdent " → " "∞" "] " e:term:67 : term =>
  match n with
  | `(binderIdent| _) => `(Filter.limUnder Filter.atTop fun _ => $e)
  | `(binderIdent| $n:ident) => `(Filter.limUnder Filter.atTop fun $n => $e)
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 1003) "lim " "[" "(" n:ident " : " ty:term ")" " → " "∞" "] " e:term:67 : term =>
  `(Filter.limUnder Filter.atTop fun $n : $ty => $e)

/-- `lim [n → -∞] e` — limit of `e` as `n` tends to `-∞` (`atBot`).
The type of `n` is inferred, or written `lim [(n : α) → -∞] e`.
Expands to `Filter.limUnder Filter.atBot fun n => e`. -/
macro:max (priority := 1003) "lim " "[" n:binderIdent " → " "-" "∞" "] " e:term:67 : term =>
  match n with
  | `(binderIdent| _) => `(Filter.limUnder Filter.atBot fun _ => $e)
  | `(binderIdent| $n:ident) => `(Filter.limUnder Filter.atBot fun $n => $e)
  | _ => Lean.Macro.throwUnsupported

macro:max (priority := 1003) "lim " "[" "(" n:ident " : " ty:term ")" " → " "-" "∞" "] " e:term:67 : term =>
  `(Filter.limUnder Filter.atBot fun $n : $ty => $e)

