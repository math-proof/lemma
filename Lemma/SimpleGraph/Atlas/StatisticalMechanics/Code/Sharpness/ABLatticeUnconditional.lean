import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.ABLatticeUnconditional
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.Sharpness


/--
[mem_ablBoxFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABLatticeUnconditional.lean)
-/
@[path]
private lemma mem_ablBoxFinset_eq
  {d n : Nat}
  {x : Site d} :
-- imply
  x ∈ ablBoxFinset d n ↔ x ∈ box d n := by
-- proof
  apply StatMech.Sharpness.mem_ablBoxFinset

/--
[zero_mem_ablBoxFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABLatticeUnconditional.lean)
-/
@[path]
private lemma zero_mem_ablBoxFinset_eq
  {d n : Nat} :
-- imply
  (0 : Site d) ∈ ablBoxFinset d n := by
-- proof
  apply StatMech.Sharpness.zero_mem_ablBoxFinset d n

/--
[ablBoxFinset_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABLatticeUnconditional.lean)
-/
@[path]
private lemma ablBoxFinset_mono_eq
  {d : Nat} :
-- imply
  Monotone (ablBoxFinset d) := by
-- proof
  apply StatMech.Sharpness.ablBoxFinset_mono d

/--
[ablGhostWindow_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABLatticeUnconditional.lean)
-/
@[path]
private lemma ablGhostWindow_mono_eq
  {d : Nat} :
-- imply
  Monotone (fun n => abigGhostWindow (ablBoxFinset d n)) := by
-- proof
  apply StatMech.Sharpness.ablGhostWindow_mono d

/--
[ablGhostWindow_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABLatticeUnconditional.lean)
-/
@[path]
private lemma ablGhostWindow_cover_eq
  {d : Nat}
  {F : Finset (Option (Site d))} :
-- imply
  ∃ n, F ⊆ abigGhostWindow (ablBoxFinset d n) := by
-- proof
  apply StatMech.Sharpness.ablGhostWindow_cover d F

/--
[abl_row_comp_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABLatticeUnconditional.lean)
-/
@[path]
private lemma abl_row_comp_translate_eq
  {d : Nat}
  {J : Sym2 (Site d) → Real}
  {x : Site d}
-- given
  (hJinv : ∀ x u v, J s(FK.fktc_translate x u, FK.fktc_translate x v) = J s(u, v)) :
-- imply
  (fun y => if (hypercubicLattice d).Adj x y then J s(x, y) else 0) ∘ FK.fktc_translate x = fun y => if (hypercubicLattice d).Adj (0 : Site d) y then J s(0, y) else 0 := by
-- proof
  apply StatMech.Sharpness.abl_row_comp_translate J hJinv x

/--
[abl_row_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABLatticeUnconditional.lean)
-/
@[path]
private lemma abl_row_summable_eq
  {d : Nat}
  {J : Sym2 (Site d) → Real}
  {x : Site d}
-- given
  (hJinv : ∀ x u v, J s(FK.fktc_translate x u, FK.fktc_translate x v) = J s(u, v))
  (hsum0 : Summable (fun y => if (hypercubicLattice d).Adj (0 : Site d) y then J s(0, y) else 0)) :
-- imply
  Summable (fun y => if (hypercubicLattice d).Adj x y then J s(x, y) else 0) := by
-- proof
  apply StatMech.Sharpness.abl_row_summable J hJinv hsum0 x

/--
[abl_row_tsum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABLatticeUnconditional.lean)
-/
@[path]
private lemma abl_row_tsum_eq_eq
  {d : Nat}
  {J : Sym2 (Site d) → Real}
  {x : Site d}
-- given
  (hJinv : ∀ x u v, J s(FK.fktc_translate x u, FK.fktc_translate x v) = J s(u, v)) :
-- imply
  (∑' y, if (hypercubicLattice d).Adj x y then J s(x, y) else 0) = ∑' y, if (hypercubicLattice d).Adj (0 : Site d) y then J s(0, y) else 0 := by
-- proof
  apply StatMech.Sharpness.abl_row_tsum_eq J hJinv x

/--
[abl_aizenmanBarsky_hypercubic_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABLatticeUnconditional.lean)
-/
@[path]
private lemma abl_aizenmanBarsky_hypercubic_unconditional_eq
  {d : Nat}
  {J : Sym2 (Site d) → Real}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hJsupport : ∀ x y, ¬ (hypercubicLattice d).Adj x y → J s(x, y) = 0)
  (hJinv : ∀ x u v, J s(FK.fktc_translate x u, FK.fktc_translate x v) = J s(u, v))
  (hsum0 : Summable (fun y => if (hypercubicLattice d).Adj (0 : Site d) y then J s(0, y) else 0)) :
-- imply
  AizenmanBarskyInequalityPhysical (abigMag (hypercubicLattice d) J (0 : Site d)) (∑' y, if (hypercubicLattice d).Adj (0 : Site d) y then J s(0, y) else 0) := by
-- proof
  apply StatMech.Sharpness.abl_aizenmanBarsky_hypercubic_unconditional J hJ hJsupport hJinv hsum0

/--
[abl_origin_row_tsum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABLatticeUnconditional.lean)
-/
@[path]
private lemma abl_origin_row_tsum_eq_eq
  {d : Nat}
  {J : Sym2 (Site d) → Real}
-- given
  (hJsupport : ∀ x y, ¬ (hypercubicLattice d).Adj x y → J s(x, y) = 0) :
-- imply
  (∑' y, if (hypercubicLattice d).Adj (0 : Site d) y then J s(0, y) else 0) = ∑' y, J s((0 : Site d), y) := by
-- proof
  apply StatMech.Sharpness.abl_origin_row_tsum_eq J hJsupport

/--
[abl_aizenmanBarsky_hypercubic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABLatticeUnconditional.lean)
-/
@[path]
private lemma abl_aizenmanBarsky_hypercubic_eq
  {d : Nat}
  {J : Sym2 (Site d) → Real}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hJsupport : ∀ x y, ¬ (hypercubicLattice d).Adj x y → J s(x, y) = 0)
  (hJinv : ∀ x u v, J s(FK.fktc_translate x u, FK.fktc_translate x v) = J s(u, v))
  (hsum0 : Summable (fun y => J s((0 : Site d), y))) :
-- imply
  AizenmanBarskyInequalityPhysical (abigMag (hypercubicLattice d) J (0 : Site d)) (∑' y, J s((0 : Site d), y)) := by
-- proof
  apply StatMech.Sharpness.abl_aizenmanBarsky_hypercubic J hJ hJsupport hJinv hsum0


-- created on 2026-10-23
