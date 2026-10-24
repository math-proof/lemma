import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferDominance
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[mem_canonicalCoverageExclusive_swap_of_strictDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferDominance.lean)
-/
@[path]
private lemma mem_canonicalCoverageExclusive_swap_of_strictDominance_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hdom : CanonicalTransferStrictlyDominates ends m k zero a.1.1 b.1.1) :
-- imply
  b ∈ canonicalCoverageExclusive ends m j k l zero p b a := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalCoverageExclusive_swap_of_strictDominance ends m j k l zero hloop hjk hkl hk0 p a b hdom

/--
[mem_canonicalMaskOrbitCoverage_inter_of_strictDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferDominance.lean)
-/
@[path]
private lemma mem_canonicalMaskOrbitCoverage_inter_of_strictDominance_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b)
  (hdom : CanonicalTransferStrictlyDominates ends m k zero a.1.1 b.1.1) :
-- imply
  a ∈ canonicalMaskOrbitCoverage ends m j k l zero p a ∧ a ∈ canonicalMaskOrbitCoverage ends m j k l zero p b := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalMaskOrbitCoverage_inter_of_strictDominance ends m j k l zero hloop hjk hkl hk0 p a b hab hdom


-- created on 2026-10-23
