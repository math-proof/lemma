import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageDirected.Part3
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[mem_canonicalMaskOrbitCoverage_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageDirected.lean)
-/
@[path]
private lemma mem_canonicalMaskOrbitCoverage_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r d : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  d ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ↔ CanonicalMaskTransferOrbit ends m j k l zero p r d ∧ CanonicalTransferWorks ends m k zero r.1.1 d.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalMaskOrbitCoverage_iff ends m j k l zero p r d

/--
[mem_canonicalMaskOrbitCoverageUnion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageDirected.lean)
-/
@[path]
private lemma mem_canonicalMaskOrbitCoverageUnion_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r s d : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  d ∈ canonicalMaskOrbitCoverageUnion ends m j k l zero p r s ↔ d ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ∨ d ∈ canonicalMaskOrbitCoverage ends m j k l zero p s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalMaskOrbitCoverageUnion_iff ends m j k l zero p r s d

/--
[canonicalMaskOrbitMaxCoverageReference_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageDirected.lean)
-/
@[path]
private lemma canonicalMaskOrbitMaxCoverageReference_spec_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  canonicalMaskOrbitMaxCoverageReference ends m j k l zero p c ∈ canonicalMaskTransferOrbitFinset ends m j k l zero p c ∧ ∀ d ∈ canonicalMaskTransferOrbitFinset ends m j k l zero p c, #(canonicalMaskOrbitCoverage ends m j k l zero p d) ≤ #(canonicalMaskOrbitCoverage ends m j k l zero p (canonicalMaskOrbitMaxCoverageReference ends m j k l zero p c)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitMaxCoverageReference_spec ends m j k l zero p c

/--
[canonicalMaskOrbitMaxCoverageReference_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageDirected.lean)
-/
@[path]
private lemma canonicalMaskOrbitMaxCoverageReference_mem_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  CanonicalMaskTransferOrbit ends m j k l zero p c (canonicalMaskOrbitMaxCoverageReference ends m j k l zero p c) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitMaxCoverageReference_mem ends m j k l zero p c

/--
[canonicalMaskOrbitMaxCoverageReference_card_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageDirected.lean)
-/
@[path]
private lemma canonicalMaskOrbitMaxCoverageReference_card_ge_eq
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
  #(canonicalMaskOrbitCoverage ends m j k l zero p d) ≤ #(canonicalMaskOrbitCoverage ends m j k l zero p (canonicalMaskOrbitMaxCoverageReference ends m j k l zero p c)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitMaxCoverageReference_card_ge ends m j k l zero p c d hcd

/--
[canonicalMaskOrbitHasCommonReference_of_coverageDirected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageDirected.lean)
-/
@[path]
private lemma canonicalMaskOrbitHasCommonReference_of_coverageDirected_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hdirected : CanonicalMaskOrbitCoverageDirected ends m j k l zero p) :
-- imply
  CanonicalMaskOrbitHasCommonReference ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitHasCommonReference_of_coverageDirected ends m j k l zero hloop hjk hkl hk0 p hdirected

/--
[GrahamFiberMinor_of_canonicalMaskOrbitCoverageDirected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageDirected.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_canonicalMaskOrbitCoverageDirected_eq
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
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_canonicalMaskOrbitCoverageDirected ends m j k l zero hloop hjk hkl hk0 hdirected


-- created on 2026-10-23
