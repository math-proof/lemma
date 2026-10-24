import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamTightRootCutHallEquivalence
open StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[canonicalMaskRightTightRootCutCoverageMerge_iff_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightRootCutHallEquivalence.lean)
-/
@[path]
private lemma canonicalMaskRightTightRootCutCoverageMerge_iff_hall_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero) :
-- imply
  CanonicalMaskRightTightRootCutCoverageMerge ends m j k l zero p ↔ CanonicalMaskRightHall ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightTightRootCutCoverageMerge_iff_hall ends m j k l zero hloop hjk hkl hk0 p

/--
[canonicalMaskRightTightRootCutCoverageMerge_iff_exists_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightRootCutHallEquivalence.lean)
-/
@[path]
private lemma canonicalMaskRightTightRootCutCoverageMerge_iff_exists_matching_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero) :
-- imply
  CanonicalMaskRightTightRootCutCoverageMerge ends m j k l zero p ↔ ∃ f : leftMaskFiber ends m j k l zero p ↪ rightMaskFiber ends m j k l zero p, ∀ c, f c ∈ canonicalMaskRightImages ends m j k l zero p c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightTightRootCutCoverageMerge_iff_exists_matching ends m j k l zero hloop hjk hkl hk0 p

/--
[tightRootCutCoverageMerge_all_iff_canonicalMaskRightHall_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightRootCutHallEquivalence.lean)
-/
@[path]
private lemma tightRootCutCoverageMerge_all_iff_canonicalMaskRightHall_all_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero) :
-- imply
  (∀ p : Finset I × Finset I, CanonicalMaskRightTightRootCutCoverageMerge ends m j k l zero p) ↔ ∀ p : Finset I × Finset I, CanonicalMaskRightHall ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.tightRootCutCoverageMerge_all_iff_canonicalMaskRightHall_all ends m j k l zero hloop hjk hkl hk0


-- created on 2026-10-23
