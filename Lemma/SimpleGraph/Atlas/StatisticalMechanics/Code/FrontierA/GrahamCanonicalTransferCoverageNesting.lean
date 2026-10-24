import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageNesting
open StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor StatMech.FrontierA


/--
[canonicalMaskOrbitCoverageNested_iff_noIncomparablePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageNesting.lean)
-/
@[path]
private lemma canonicalMaskOrbitCoverageNested_iff_noIncomparablePair_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  CanonicalMaskOrbitCoverageNested ends m j k l zero p ↔ CanonicalMaskOrbitCoverageNoIncomparablePair ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitCoverageNested_iff_noIncomparablePair ends m j k l zero p

/--
[canonicalMaskOrbitCoverageDirected_of_nested](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageNesting.lean)
-/
@[path]
private lemma canonicalMaskOrbitCoverageDirected_of_nested_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hnested : CanonicalMaskOrbitCoverageNested ends m j k l zero p) :
-- imply
  CanonicalMaskOrbitCoverageDirected ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitCoverageDirected_of_nested ends m j k l zero p hnested

/--
[GrahamFiberMinor_of_canonicalMaskOrbitCoverageNested](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageNesting.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_canonicalMaskOrbitCoverageNested_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hnested : ∀ p : Finset I × Finset I, CanonicalMaskOrbitCoverageNested ends m j k l zero p) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_canonicalMaskOrbitCoverageNested ends m j k l zero hloop hjk hkl hk0 hnested

/--
[GrahamFiberMinor_of_canonicalMaskOrbitCoverageNoIncomparablePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageNesting.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_canonicalMaskOrbitCoverageNoIncomparablePair_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : ∀ p : Finset I × Finset I, CanonicalMaskOrbitCoverageNoIncomparablePair ends m j k l zero p) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_canonicalMaskOrbitCoverageNoIncomparablePair ends m j k l zero hloop hjk hkl hk0 hno

/--
[rowDataRepairHall_of_canonicalMaskOrbitCoverageNested](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageNesting.lean)
-/
@[path]
private lemma rowDataRepairHall_of_canonicalMaskOrbitCoverageNested_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hnested : ∀ p : Finset I × Finset I, CanonicalMaskOrbitCoverageNested ends m j k l zero p) :
-- imply
  RowDataRepairHall ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairHall_of_canonicalMaskOrbitCoverageNested ends m j k l zero hloop hjk hkl hk0 hnested

/--
[GrahamWeightedRowMinor_of_canonicalMaskOrbitCoverageNested](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageNesting.lean)
-/
@[path]
private lemma GrahamWeightedRowMinor_of_canonicalMaskOrbitCoverageNested_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hnested : ∀ p : Finset I × Finset I, CanonicalMaskOrbitCoverageNested ends m j k l zero p) :
-- imply
  GrahamWeightedRowMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamWeightedRowMinor_of_canonicalMaskOrbitCoverageNested ends m j k l zero hloop hjk hkl hk0 hnested

/--
[grahamWeightedLemmaOne_of_canonicalMaskOrbitCoverageNested](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageNesting.lean)
-/
@[path]
private lemma grahamWeightedLemmaOne_of_canonicalMaskOrbitCoverageNested_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hkm : k ≠ m)
  (hnested : ∀ total : G.edgeFinset -> Nat, ∀ p : Finset (Copy G total) × Finset (Copy G total), CanonicalMaskOrbitCoverageNested (endsM G total) Finset.univ j k l m p) :
-- imply
  sourcePairDisconnSum G beta J {j, k} ∅ k m * sourcePairDisconnSum G beta J {k, l} ∅ k m <= sourcePairDisconnSum G beta J {j, k} {k, l} k m * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.grahamWeightedLemmaOne_of_canonicalMaskOrbitCoverageNested G beta J hbeta hJ j k l m hjk hkl hkm hnested

/--
[grahamWeightedLemmaOne_of_canonicalMaskOrbitCoverageNestedAllMarks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageNesting.lean)
-/
@[path]
private lemma grahamWeightedLemmaOne_of_canonicalMaskOrbitCoverageNestedAllMarks_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hkm : k ≠ m)
  (hnested : ∀ total : G.edgeFinset -> Nat, CanonicalMaskOrbitCoverageNestedAllMarks (endsM G total) Finset.univ) :
-- imply
  sourcePairDisconnSum G beta J {j, k} ∅ k m * sourcePairDisconnSum G beta J {k, l} ∅ k m <= sourcePairDisconnSum G beta J {j, k} {k, l} k m * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.grahamWeightedLemmaOne_of_canonicalMaskOrbitCoverageNestedAllMarks G beta J hbeta hJ j k l m hjk hkl hkm hnested


-- created on 2026-10-23
