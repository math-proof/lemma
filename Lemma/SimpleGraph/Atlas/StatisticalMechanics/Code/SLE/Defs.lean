import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.SLE.Defs
open MeasureTheory ProbabilityTheory Complex Filter Topology StatMech StatMech.SLE


/--
[mem_upperHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean)
-/
@[path]
private lemma mem_upperHalfPlane_eq
  {z : ℂ} :
-- imply
  z ∈ upperHalfPlane ↔ 0 < z.im := by
-- proof
  apply StatMech.SLE.mem_upperHalfPlane

/--
[isOpen_upperHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean)
-/
@[path]
private lemma isOpen_upperHalfPlane_eq :
-- imply
  IsOpen upperHalfPlane := by
-- proof
  apply StatMech.SLE.isOpen_upperHalfPlane

/--
[mem_closedUpperHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean)
-/
@[path]
private lemma mem_closedUpperHalfPlane_eq
  {z : ℂ} :
-- imply
  z ∈ closedUpperHalfPlane ↔ 0 ≤ z.im := by
-- proof
  apply StatMech.SLE.mem_closedUpperHalfPlane

/--
[isClosed_closedUpperHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean)
-/
@[path]
private lemma isClosed_closedUpperHalfPlane_eq :
-- imply
  IsClosed closedUpperHalfPlane := by
-- proof
  apply StatMech.SLE.isClosed_closedUpperHalfPlane

/--
[upperHalfPlane_subset_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean)
-/
@[path]
private lemma upperHalfPlane_subset_closed_eq :
-- imply
  upperHalfPlane ⊆ closedUpperHalfPlane := by
-- proof
  apply StatMech.SLE.upperHalfPlane_subset_closed

/--
[mem_realLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean)
-/
@[path]
private lemma mem_realLine_eq
  {z : ℂ} :
-- imply
  z ∈ realLine ↔ z.im = 0 := by
-- proof
  apply StatMech.SLE.mem_realLine

/--
[ofReal_mem_realLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean)
-/
@[path]
private lemma ofReal_mem_realLine_eq
  {x : ℝ} :
-- imply
  (x : ℂ) ∈ realLine := by
-- proof
  apply StatMech.SLE.ofReal_mem_realLine x

/--
[isCompactHull_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean)
-/
@[path]
private lemma isCompactHull_empty_eq :
-- imply
  IsCompactHull (∅ : Set ℂ) where subset := by
-- proof
  apply StatMech.SLE.isCompactHull_empty

/--
[hasHalfPlaneCapacity_id](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean)
-/
@[path]
private lemma hasHalfPlaneCapacity_id_eq :
-- imply
  HasHalfPlaneCapacity id 0 := by
-- proof
  apply StatMech.SLE.hasHalfPlaneCapacity_id

/--
[HasHalfPlaneCapacity.unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean)
-/
@[path]
private lemma unique_eq
  {g : ℂ → ℂ}
  {a b : ℝ}
-- given
  (ha : HasHalfPlaneCapacity g a)
  (hb : HasHalfPlaneCapacity g b) :
-- imply
  a = b := by
-- proof
  apply StatMech.SLE.HasHalfPlaneCapacity.unique ha hb

/--
[loewnerField_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean)
-/
@[path]
private lemma loewnerField_apply_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {w : ℂ} :
-- imply
  loewnerField W t w = 2 / (w - (W t : ℂ)) := by
-- proof
  apply StatMech.SLE.loewnerField_apply W t w

/--
[LoewnerChain.continuous_driving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean)
-/
@[path]
private lemma continuous_driving_eq
  {c : LoewnerChain} :
-- imply
  Continuous c.driving := by
-- proof
  apply StatMech.SLE.LoewnerChain.continuous_driving c

/--
[LoewnerChain.maps_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean)
-/
@[path]
private lemma maps_zero_eq
  {c : LoewnerChain}
  {z : ℂ} :
-- imply
  c.maps 0 z = z := by
-- proof
  apply StatMech.SLE.LoewnerChain.maps_zero c z

/--
[sleDriving_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean)
-/
@[path]
private lemma sleDriving_apply_eq
  {κ : ℝ}
  {B : ℝ → Ω → ℝ}
  {ω : Ω}
  {t : ℝ} :
-- imply
  sleDriving κ B ω t = Real.sqrt κ * B t ω := by
-- proof
  apply StatMech.SLE.sleDriving_apply κ B ω t

/--
[sleDriving_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean)
-/
@[path]
private lemma sleDriving_zero_eq
  {κ : ℝ}
  {B : ℝ → Ω → ℝ}
  {ω : Ω} :
-- imply
  sleDriving κ B ω 0 = Real.sqrt κ * B 0 ω := by
-- proof
  apply StatMech.SLE.sleDriving_zero κ B ω

/--
[sleDriving_kappa_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean)
-/
@[path]
private lemma sleDriving_kappa_zero_eq
  {B : ℝ → Ω → ℝ}
  {ω : Ω}
  {t : ℝ} :
-- imply
  sleDriving 0 B ω t = 0 := by
-- proof
  apply StatMech.SLE.sleDriving_kappa_zero B ω t


-- created on 2026-10-23
