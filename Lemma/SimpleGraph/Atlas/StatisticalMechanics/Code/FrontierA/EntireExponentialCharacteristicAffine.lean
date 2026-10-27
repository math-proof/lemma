import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.EntireExponentialCharacteristicAffine
open Filter Metric Real Set Topology ValueDistribution StatMech StatMech.FrontierA


/--
[re_apply_le_three_mul_proximity_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/EntireExponentialCharacteristicAffine.lean)
-/
@[path]
private lemma re_apply_le_three_mul_proximity_exp_eq
  {g : Complex → Complex}
  {R : Real}
  {w : Complex}
-- given
  (hg : Differentiable Complex g)
  (hR : 0 < R)
  (hw : ‖w‖ ≤ R / 2) :
-- imply
  (g w).re ≤ 3 * proximity (fun z ↦ Complex.exp (g z)) ⊤ R := by
-- proof
  apply StatMech.FrontierA.re_apply_le_three_mul_proximity_exp g hg hR hw

/--
[exists_affine_of_entire_exp_proximity_growth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/EntireExponentialCharacteristicAffine.lean)
-/
@[path]
private lemma exists_affine_of_entire_exp_proximity_growth_eq
  {g : Complex → Complex}
  {C D : Real}
-- given
  (hg : Differentiable Complex g)
  (hD : 0 ≤ D)
  (hgrowth : ∀ R : Real, 1 ≤ R → proximity (fun z ↦ Complex.exp (g z)) ⊤ R ≤ C + D * R) :
-- imply
  ∃ a b : Complex, ∀ z, g z = a * z + b := by
-- proof
  apply StatMech.FrontierA.exists_affine_of_entire_exp_proximity_growth g hg C D hD hgrowth

/--
[proximity_top_le_of_exp_growth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/EntireExponentialCharacteristicAffine.lean)
-/
@[path]
private lemma proximity_top_le_of_exp_growth_eq
  {f : Complex → Complex}
  {A B R : Real}
-- given
  (hf : Differentiable Complex f)
  (_hA : 0 < A)
  (hB : 0 ≤ B)
  (hR : 1 ≤ R)
  (hgrowth : ∀ z, ‖f z‖ ≤ A * Real.exp (B * ‖z‖)) :
-- imply
  proximity f ⊤ R ≤ log⁺ A + B * R := by
-- proof
  apply StatMech.FrontierA.proximity_top_le_of_exp_growth f hf A B R _hA hB hR hgrowth

/--
[exists_affine_of_matched_entire_exp_growth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/EntireExponentialCharacteristicAffine.lean)
-/
@[path]
private lemma exists_affine_of_matched_entire_exp_growth_eq
  {f p g : Complex → Complex}
  {Af Bf Ap Bp : Real}
-- given
  (hf : Differentiable Complex f)
  (hp : Differentiable Complex p)
  (hg : Differentiable Complex g)
  (hp0 : p 0 ≠ 0)
  (hfactor : ∀ z, f z = p z * Complex.exp (g z))
  (hAf : 0 < Af)
  (hBf : 0 ≤ Bf)
  (hAp : 0 < Ap)
  (hBp : 0 ≤ Bp)
  (hfGrowth : ∀ z, ‖f z‖ ≤ Af * Real.exp (Bf * ‖z‖))
  (hpGrowth : ∀ z, ‖p z‖ ≤ Ap * Real.exp (Bp * ‖z‖)) :
-- imply
  ∃ a b : Complex, ∀ z, g z = a * z + b := by
-- proof
  apply StatMech.FrontierA.exists_affine_of_matched_entire_exp_growth f p g hf hp hg hp0 hfactor Af Bf Ap Bp hAf hBf hAp hBp hfGrowth hpGrowth


-- created on 2026-10-23
