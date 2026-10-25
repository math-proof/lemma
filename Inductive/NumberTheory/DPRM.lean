/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DPRM.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Computability.RE
import Mathlib.NumberTheory.Dioph
import Mathlib.Computability.Primrec.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Logic.Godel.GodelBetaFunction
import Mathlib.Tactic
open scoped Dioph Vector3 Nat Function


namespace MathlibExt.NumberTheory.DPRMWanted

/-- Natural-number polynomial expressions in variables `γ`. -/
inductive dpNatPoly {γ : Type} : ((γ → ℕ) → ℕ) → Prop
  | var (i : γ) : dpNatPoly (fun v => v i)
  | const (n : ℕ) : dpNatPoly (fun _ => n)
  | add {F₁ F₂ : (γ → ℕ) → ℕ} :
      dpNatPoly F₁ → dpNatPoly F₂ → dpNatPoly (fun v => F₁ v + F₂ v)
  | mul {F₁ F₂ : (γ → ℕ) → ℕ} :
      dpNatPoly F₁ → dpNatPoly F₂ → dpNatPoly (fun v => F₁ v * F₂ v)

end MathlibExt.NumberTheory.DPRMWanted
