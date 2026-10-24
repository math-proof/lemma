import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferPairExpansion
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[canonicalTransferSymmDiff_card_le_m](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferPairExpansion.lean)
-/
@[path]
private lemma canonicalTransferSymmDiff_card_le_m_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  #(canonicalTransferUnion ends m k zero a.1.1 ∆ canonicalTransferUnion ends m k zero b.1.1) ≤ #m := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferSymmDiff_card_le_m hloop hjk hkl a b

/--
[canonicalCoveragePairScore_lt_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferPairExpansion.lean)
-/
@[path]
private lemma canonicalCoveragePairScore_lt_iff_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c d : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  canonicalCoveragePairScore ends m k zero a.1.1 b.1.1 < canonicalCoveragePairScore ends m k zero c.1.1 d.1.1 ↔ #(rowClass m a.1.1 0 ∆ rowClass m b.1.1 0) < #(rowClass m c.1.1 0 ∆ rowClass m d.1.1 0) ∨ (#(rowClass m a.1.1 0 ∆ rowClass m b.1.1 0) = #(rowClass m c.1.1 0 ∆ rowClass m d.1.1 0) ∧ #(canonicalTransferUnion ends m k zero a.1.1 ∆ canonicalTransferUnion ends m k zero b.1.1) < #(canonicalTransferUnion ends m k zero c.1.1 ∆ canonicalTransferUnion ends m k zero d.1.1)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalCoveragePairScore_lt_iff hloop hjk hkl a b c d

/--
[canonicalMaskOrbitCoveragePairProgress_of_pairExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferPairExpansion.lean)
-/
@[path]
private lemma canonicalMaskOrbitCoveragePairProgress_of_pairExpansion_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hexpand : CanonicalMaskOrbitCoveragePairExpansion ends m j k l zero p) :
-- imply
  CanonicalMaskOrbitCoveragePairProgress ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitCoveragePairProgress_of_pairExpansion ends m j k l zero p hexpand

/--
[mem_canonicalCoveragePairCandidates_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferPairExpansion.lean)
-/
@[path]
private lemma mem_canonicalCoveragePairCandidates_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r s a b : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  (a, b) ∈ canonicalCoveragePairCandidates ends m j k l zero p r s ↔ CanonicalMaskTransferOrbit ends m j k l zero p r a ∧ CanonicalMaskTransferOrbit ends m j k l zero p r b ∧ canonicalMaskOrbitCoverageUnion ends m j k l zero p a b = canonicalMaskOrbitCoverageUnion ends m j k l zero p r s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalCoveragePairCandidates_iff ends m j k l zero p r s a b

/--
[canonicalCoveragePairCandidates_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferPairExpansion.lean)
-/
@[path]
private lemma canonicalCoveragePairCandidates_nonempty_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r s : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hrs : CanonicalMaskTransferOrbit ends m j k l zero p r s) :
-- imply
  (canonicalCoveragePairCandidates ends m j k l zero p r s).Nonempty := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalCoveragePairCandidates_nonempty ends m j k l zero p r s hrs

/--
[canonicalMaskOrbitCoverageUnionClosed_of_pairProgress](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferPairExpansion.lean)
-/
@[path]
private lemma canonicalMaskOrbitCoverageUnionClosed_of_pairProgress_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hprogress : CanonicalMaskOrbitCoveragePairProgress ends m j k l zero p) :
-- imply
  CanonicalMaskOrbitCoverageUnionClosed ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitCoverageUnionClosed_of_pairProgress ends m j k l zero p hprogress

/--
[canonicalMaskOrbitCoverageUnionClosed_of_pairExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferPairExpansion.lean)
-/
@[path]
private lemma canonicalMaskOrbitCoverageUnionClosed_of_pairExpansion_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hexpand : CanonicalMaskOrbitCoveragePairExpansion ends m j k l zero p) :
-- imply
  CanonicalMaskOrbitCoverageUnionClosed ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitCoverageUnionClosed_of_pairExpansion ends m j k l zero p hexpand


-- created on 2026-10-23
