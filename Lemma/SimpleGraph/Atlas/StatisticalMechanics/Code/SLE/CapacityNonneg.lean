import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.SLE.CapacityNonneg
open Filter Topology Complex Bornology StatMech StatMech.SLE


/--
[tendsto_imagRay_cocompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityNonneg.lean)
-/
@[path]
private lemma tendsto_imagRay_cocompact_eq :
-- imply
  Tendsto (fun y : ℝ => Complex.I * (y : ℂ)) atTop (cocompact ℂ) := by
-- proof
  apply StatMech.SLE.tendsto_imagRay_cocompact

/--
[re_imagRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityNonneg.lean)
-/
@[path]
private lemma re_imagRay_eq
  {g : ℂ → ℂ}
  {y : ℝ} :
-- imply
  (Complex.I * (y : ℂ) * (g (Complex.I * (y : ℂ)) - Complex.I * (y : ℂ))).re = y * (y - (g (Complex.I * (y : ℂ))).im) := by
-- proof
  apply StatMech.SLE.re_imagRay g y

/--
[hcap_nonneg_of_shrinksIm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityNonneg.lean)
-/
@[path]
private lemma hcap_nonneg_of_shrinksIm_eq
  {g : ℂ → ℂ}
  {a : ℝ}
-- given
  (hg : HasHalfPlaneCapacity g a)
  (hshrink : ShrinksIm g) :
-- imply
  0 ≤ a := by
-- proof
  apply StatMech.SLE.hcap_nonneg_of_shrinksIm hg hshrink

/--
[shrinksIm_neg_example_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityNonneg.lean)
-/
@[path]
private lemma shrinksIm_neg_example_false_eq :
-- imply
  ¬ ShrinksIm (fun z : ℂ => z - z⁻¹) := by
-- proof
  apply StatMech.SLE.shrinksIm_neg_example_false

/--
[shrinksIm_halfDisk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityNonneg.lean)
-/
@[path]
private lemma shrinksIm_halfDisk_eq
  {c : ℝ}
-- given
  (hc : 0 ≤ c) :
-- imply
  ShrinksIm (fun z : ℂ => z + (c : ℂ) / z) := by
-- proof
  apply StatMech.SLE.shrinksIm_halfDisk hc

/--
[hcap_halfDisk_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityNonneg.lean)
-/
@[path]
private lemma hcap_halfDisk_nonneg_eq
  {c : ℝ}
-- given
  (hc : 0 ≤ c) :
-- imply
  (0 : ℝ) ≤ c := by
-- proof
  apply StatMech.SLE.hcap_halfDisk_nonneg hc

/--
[le_of_comp_of_shrinksIm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityNonneg.lean)
-/
@[path]
private lemma le_of_comp_of_shrinksIm_eq
  {g h g' : ℂ → ℂ}
  {a b a' : ℝ}
-- given
  (hg : HasHalfPlaneCapacity g a)
  (hh : HasHalfPlaneCapacity h b)
  (hhull : ShrinksIm h)
  (hfac : g' = h ∘ g)
  (hg' : HasHalfPlaneCapacity g' a') :
-- imply
  a ≤ a' := by
-- proof
  apply StatMech.SLE.le_of_comp_of_shrinksIm hg hh hhull hfac hg'


-- created on 2026-10-23
