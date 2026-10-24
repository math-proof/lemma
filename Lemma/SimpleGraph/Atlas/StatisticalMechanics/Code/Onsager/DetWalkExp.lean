import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.DetWalkExp
open StatMech StatMech.Onsager


/--
[ons_maskMatrix_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DetWalkExp.lean)
-/
@[path]
private lemma ons_maskMatrix_union_eq
  [DecidableEq E]
  {S T : Finset E}
  {Λ : Matrix E E ℂ} :
-- imply
  ons_maskMatrix S (ons_maskMatrix T Λ) = ons_maskMatrix (S ∪ T) Λ := by
-- proof
  apply StatMech.Onsager.ons_maskMatrix_union S T Λ

/--
[ons_loopWeight_maskMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DetWalkExp.lean)
-/
@[path]
private lemma ons_loopWeight_maskMatrix_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {forbidden : Finset E}
  {Λ : Matrix E E ℂ}
  {d : Fin n → E} :
-- imply
  ons_loopWeight (ons_maskMatrix forbidden Λ) d = if ∃ k, d k ∈ forbidden then 0 else ons_loopWeight Λ d := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_maskMatrix forbidden Λ d

/--
[ons_loopSum_maskMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DetWalkExp.lean)
-/
@[path]
private lemma ons_loopSum_maskMatrix_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {forbidden : Finset E}
  {Λ : Matrix E E ℂ} :
-- imply
  (∑ d : Fin n → E, ons_loopWeight (ons_maskMatrix forbidden Λ) d) = ∑ d ∈ Finset.univ.filter (fun d : Fin n → E => ¬ ∃ k, d k ∈ forbidden), ons_loopWeight Λ d := by
-- proof
  apply StatMech.Onsager.ons_loopSum_maskMatrix forbidden Λ

/--
[ons_det_eq_walk_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DetWalkExp.lean)
-/
@[path]
private lemma ons_det_eq_walk_exp_eq
  [Fintype E]
  [DecidableEq E]
  {Λ : Matrix E E ℂ}
-- given
  (hspec : ∀ α ∈ Λ.charpoly.roots, ‖α‖ < 1) :
-- imply
  (1 - Λ).det = Complex.exp (- ∑' n : ℕ, (∑ v : Fin (n + 1) → E, ∏ k : Fin (n + 1), Λ (v k) (v (k + 1))) / (n + 1)) := by
-- proof
  apply StatMech.Onsager.ons_det_eq_walk_exp Λ hspec

/--
[ons_detWalkRoot_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DetWalkExp.lean)
-/
@[path]
private lemma ons_detWalkRoot_sq_eq
  [Fintype E]
  [DecidableEq E]
  {Λ : Matrix E E ℂ}
-- given
  (hspec : ∀ α ∈ Λ.charpoly.roots, ‖α‖ < 1) :
-- imply
  ons_detWalkRoot Λ ^ 2 = (1 - Λ).det := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_sq Λ hspec

/--
[ons_detWalkRoot_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DetWalkExp.lean)
-/
@[path]
private lemma ons_detWalkRoot_zero_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  ons_detWalkRoot (0 : Matrix E E ℂ) = 1 := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_zero


-- created on 2026-10-23
