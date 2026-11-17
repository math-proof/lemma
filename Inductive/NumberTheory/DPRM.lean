/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DPRM.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Computability.RE
public import Mathlib.NumberTheory.Dioph
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Int.GCD
public import Mathlib.Logic.Godel.GodelBetaFunction
public import Mathlib.Tactic
open scoped Dioph Vector3 Nat Function


namespace MathlibExt.NumberTheory.DPRMWanted

/-- Natural-number polynomial expressions in variables `γ`. -/
public inductive dpNatPoly {γ : Type} : ((γ → ℕ) → ℕ) → Prop
  | var (i : γ) : dpNatPoly (fun v => v i)
  | const (n : ℕ) : dpNatPoly (fun _ => n)
  | add {F₁ F₂ : (γ → ℕ) → ℕ} :
      dpNatPoly F₁ → dpNatPoly F₂ → dpNatPoly (fun v => F₁ v + F₂ v)
  | mul {F₁ F₂ : (γ → ℕ) → ℕ} :
      dpNatPoly F₁ → dpNatPoly F₂ → dpNatPoly (fun v => F₁ v * F₂ v)

end MathlibExt.NumberTheory.DPRMWanted
