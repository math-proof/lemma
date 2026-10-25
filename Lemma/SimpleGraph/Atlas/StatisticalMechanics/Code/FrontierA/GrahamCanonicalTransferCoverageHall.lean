import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageHall
open StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[rowDataRepairHall_of_canonicalMaskOrbitCoverageDirected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageHall.lean)
-/
@[path]
private lemma rowDataRepairHall_of_canonicalMaskOrbitCoverageDirected_eq
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
  (hdirected : ∀ p : Finset I × Finset I, CanonicalMaskOrbitCoverageDirected ends m j k l zero p) :
-- imply
  RowDataRepairHall ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataRepairHall_of_canonicalMaskOrbitCoverageDirected ends m j k l zero hloop hjk hkl hk0 hdirected

/--
[GrahamWeightedRowMinor_of_canonicalMaskOrbitCoverageDirected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageHall.lean)
-/
@[path]
private lemma GrahamWeightedRowMinor_of_canonicalMaskOrbitCoverageDirected_eq
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
  (hdirected : ∀ p : Finset I × Finset I, CanonicalMaskOrbitCoverageDirected ends m j k l zero p) :
-- imply
  GrahamWeightedRowMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamWeightedRowMinor_of_canonicalMaskOrbitCoverageDirected ends m j k l zero hloop hjk hkl hk0 hdirected


-- created on 2026-10-23
