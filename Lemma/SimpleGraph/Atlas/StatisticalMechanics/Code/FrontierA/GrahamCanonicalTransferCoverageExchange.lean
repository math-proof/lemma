import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageExchange.Part2
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[exists_coverage_exclusive_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageExchange.lean)
-/
@[path]
private lemma exists_coverage_exclusive_witnesses_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (ha : canonicalMaskOrbitCoverage ends m j k l zero p a ≠ canonicalMaskOrbitCoverageUnion ends m j k l zero p a b)
  (hb : canonicalMaskOrbitCoverage ends m j k l zero p b ≠ canonicalMaskOrbitCoverageUnion ends m j k l zero p a b) :
-- imply
  (∃ c, c ∈ canonicalMaskOrbitCoverage ends m j k l zero p a ∧ c ∉ canonicalMaskOrbitCoverage ends m j k l zero p b) ∧ ∃ d, d ∈ canonicalMaskOrbitCoverage ends m j k l zero p b ∧ d ∉ canonicalMaskOrbitCoverage ends m j k l zero p a := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_coverage_exclusive_witnesses ends m j k l zero p a b ha hb

/--
[canonicalMaskOrbitCoverageUnion_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageExchange.lean)
-/
@[path]
private lemma canonicalMaskOrbitCoverageUnion_comm_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  canonicalMaskOrbitCoverageUnion ends m j k l zero p a b = canonicalMaskOrbitCoverageUnion ends m j k l zero p b a := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitCoverageUnion_comm ends m j k l zero p a b

/--
[canonicalMaskOrbitCoverageUnionClosed_of_smallerExclusiveJoin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageExchange.lean)
-/
@[path]
private lemma canonicalMaskOrbitCoverageUnionClosed_of_smallerExclusiveJoin_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hjoin : CanonicalMaskOrbitCoverageSmallerExclusiveJoin ends m j k l zero p) :
-- imply
  CanonicalMaskOrbitCoverageUnionClosed ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitCoverageUnionClosed_of_smallerExclusiveJoin ends m j k l zero p hjoin

/--
[mem_coverage_quadrangleCompletion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageExchange.lean)
-/
@[path]
private lemma mem_coverage_quadrangleCompletion_iff_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b)
  (hdisc : RowsDisconnect ends m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) k zero) :
-- imply
  let d := canonicalQuadrangleCompletionMemOfDisconnects ends m j k l zero hloop hjk hkl p a b c hdisc d ∈ canonicalMaskOrbitCoverage ends m j k l zero p b ↔ c ∈ canonicalMaskOrbitCoverage ends m j k l zero p a := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_coverage_quadrangleCompletion_iff hloop hjk hkl a b c hab hdisc

/--
[quadrangleCompletion_mem_coverage_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageExchange.lean)
-/
@[path]
private lemma quadrangleCompletion_mem_coverage_sdiff_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b)
  (hc : c ∈ canonicalMaskOrbitCoverage ends m j k l zero p a)
  (hcb : c ∉ canonicalMaskOrbitCoverage ends m j k l zero p b)
  (hdisc : RowsDisconnect ends m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) k zero) :
-- imply
  let d := canonicalQuadrangleCompletionMemOfDisconnects ends m j k l zero hloop hjk hkl p a b c hdisc d ∈ canonicalMaskOrbitCoverage ends m j k l zero p b ∧ d ∉ canonicalMaskOrbitCoverage ends m j k l zero p a := by
-- proof
  apply StatMech.GrahamGHS.FourColor.quadrangleCompletion_mem_coverage_sdiff hloop hjk hkl a b c hab hc hcb hdisc


-- created on 2026-10-23
