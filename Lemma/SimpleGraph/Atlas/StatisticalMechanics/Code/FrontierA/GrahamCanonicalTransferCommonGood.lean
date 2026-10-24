import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCommonGood
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[canonicalTransferWorks_iff_rowSymmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCommonGood.lean)
-/
@[path]
private lemma canonicalTransferWorks_iff_rowSymmDiff_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ↔ ¬ connK ends (rowClass m c.1.1 0 ∆ canonicalTransferUnion ends m k zero r.1.1) k zero ∧ ¬ connK ends (rowClass m c.1.1 1 ∆ canonicalTransferUnion ends m k zero r.1.1) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferWorks_iff_rowSymmDiff hloop hjk hkl r c

/--
[canonicalTransferWorks_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCommonGood.lean)
-/
@[path]
private lemma canonicalTransferWorks_self_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero) :
-- imply
  CanonicalTransferWorks ends m k zero c.1.1 c.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferWorks_self hloop hjk hkl hk0 c

/--
[mem_canonicalMaskOrbitCommonReferenceFinset_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCommonGood.lean)
-/
@[path]
private lemma mem_canonicalMaskOrbitCommonReferenceFinset_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c r : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  r ∈ canonicalMaskOrbitCommonReferenceFinset ends m j k l zero p c ↔ CanonicalMaskTransferOrbit ends m j k l zero p c r ∧ ∀ d, CanonicalMaskTransferOrbit ends m j k l zero p c d -> CanonicalTransferWorks ends m k zero r.1.1 d.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalMaskOrbitCommonReferenceFinset_iff ends m j k l zero p c r

/--
[canonicalMaskOrbitCommonReferenceFinset_eq_of_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCommonGood.lean)
-/
@[path]
private lemma canonicalMaskOrbitCommonReferenceFinset_eq_of_orbit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
-- imply
  canonicalMaskOrbitCommonReferenceFinset ends m j k l zero p c = canonicalMaskOrbitCommonReferenceFinset ends m j k l zero p d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitCommonReferenceFinset_eq_of_orbit ends m j k l zero p c d hcd

/--
[canonicalMaskOrbitCommonReference_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCommonGood.lean)
-/
@[path]
private lemma canonicalMaskOrbitCommonReference_spec_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hcommon : CanonicalMaskOrbitHasCommonReference ends m j k l zero p) :
-- imply
  canonicalMaskOrbitCommonReference ends m j k l zero p hcommon c ∈ canonicalMaskOrbitCommonReferenceFinset ends m j k l zero p c ∧ ∀ r ∈ canonicalMaskOrbitCommonReferenceFinset ends m j k l zero p c, canonicalMaskOrbitScore ends m k zero p (canonicalMaskOrbitCommonReference ends m j k l zero p hcommon c) ≤ canonicalMaskOrbitScore ends m k zero p r := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitCommonReference_spec ends m j k l zero p hcommon c

/--
[canonicalMaskOrbitCommonReference_eq_of_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCommonGood.lean)
-/
@[path]
private lemma canonicalMaskOrbitCommonReference_eq_of_orbit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hcommon : CanonicalMaskOrbitHasCommonReference ends m j k l zero p)
  (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
-- imply
  canonicalMaskOrbitCommonReference ends m j k l zero p hcommon c = canonicalMaskOrbitCommonReference ends m j k l zero p hcommon d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitCommonReference_eq_of_orbit ends m j k l zero p hcommon c d hcd

/--
[canonicalMaskOrbitCommonReference_selector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCommonGood.lean)
-/
@[path]
private lemma canonicalMaskOrbitCommonReference_selector_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hcommon : CanonicalMaskOrbitHasCommonReference ends m j k l zero p) :
-- imply
  IsCanonicalMaskOrbitSelector ends m j k l zero p (canonicalMaskOrbitCommonReference ends m j k l zero p hcommon) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitCommonReference_selector ends m j k l zero p hcommon

/--
[canonicalMaskOrbitCommonReference_works](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCommonGood.lean)
-/
@[path]
private lemma canonicalMaskOrbitCommonReference_works_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hcommon : CanonicalMaskOrbitHasCommonReference ends m j k l zero p) :
-- imply
  CanonicalTransferWorks ends m k zero (canonicalMaskOrbitCommonReference ends m j k l zero p hcommon c).1.1 c.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitCommonReference_works ends m j k l zero p hcommon c

/--
[GrahamFiberMinor_of_canonicalMaskOrbitCommonReference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCommonGood.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_canonicalMaskOrbitCommonReference_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hcommon : ∀ p : Finset I × Finset I, CanonicalMaskOrbitHasCommonReference ends m j k l zero p) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_canonicalMaskOrbitCommonReference ends m j k l zero hloop hjk hkl hcommon


-- created on 2026-10-23
