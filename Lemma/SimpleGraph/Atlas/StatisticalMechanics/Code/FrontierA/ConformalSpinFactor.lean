import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.ConformalSpinFactor
open StatMech StatMech.FrontierA


/--
[spinDerivativeFactor_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/ConformalSpinFactor.lean)
-/
@[path]
private lemma spinDerivativeFactor_mul_eq
  [Fintype ι]
  {d₁ d₂ : ι → ℂ} :
-- imply
  spinDerivativeFactor (fun i => d₁ i * d₂ i) = spinDerivativeFactor d₁ * spinDerivativeFactor d₂ := by
-- proof
  apply StatMech.FrontierA.spinDerivativeFactor_mul d₁ d₂

/--
[spinDerivativeFactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/ConformalSpinFactor.lean)
-/
@[path]
private lemma spinDerivativeFactor_pos_eq
  [Fintype ι]
  {d : ι → ℂ}
-- given
  (hd : ∀ i, d i ≠ 0) :
-- imply
  0 < spinDerivativeFactor d := by
-- proof
  apply StatMech.FrontierA.spinDerivativeFactor_pos hd

/--
[spinConformalFactor_id](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/ConformalSpinFactor.lean)
-/
@[path]
private lemma spinConformalFactor_id_eq
  [Fintype ι]
  {a : ι → ℂ} :
-- imply
  spinConformalFactor id a = 1 := by
-- proof
  apply StatMech.FrontierA.spinConformalFactor_id a

/--
[spinConformalFactor_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/ConformalSpinFactor.lean)
-/
@[path]
private lemma spinConformalFactor_comp_eq
  [Fintype ι]
  {Ψ Φ : ℂ → ℂ}
  {a : ι → ℂ}
-- given
  (hΦ : ∀ i, DifferentiableAt ℂ Φ (a i))
  (hΨ : ∀ i, DifferentiableAt ℂ Ψ (Φ (a i))) :
-- imply
  spinConformalFactor (Ψ ∘ Φ) a = spinConformalFactor Ψ (Φ ∘ a) * spinConformalFactor Φ a := by
-- proof
  apply StatMech.FrontierA.spinConformalFactor_comp Ψ Φ a hΦ hΨ

/--
[spinConformalFactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/ConformalSpinFactor.lean)
-/
@[path]
private lemma spinConformalFactor_pos_eq
  [Fintype ι]
  {Φ : ℂ → ℂ}
  {a : ι → ℂ}
-- given
  (hΦ : ∀ i, deriv Φ (a i) ≠ 0) :
-- imply
  0 < spinConformalFactor Φ a := by
-- proof
  apply StatMech.FrontierA.spinConformalFactor_pos hΦ


-- created on 2026-10-23
