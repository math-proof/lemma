import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageJoin
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[mem_canonicalMaskOrbitCoverageJoinCandidates_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageJoin.lean)
-/
@[path]
private lemma mem_canonicalMaskOrbitCoverageJoinCandidates_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r s t : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  t ∈ canonicalMaskOrbitCoverageJoinCandidates ends m j k l zero p r s ↔ CanonicalMaskTransferOrbit ends m j k l zero p r t ∧ canonicalMaskOrbitCoverage ends m j k l zero p t = canonicalMaskOrbitCoverageUnion ends m j k l zero p r s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalMaskOrbitCoverageJoinCandidates_iff ends m j k l zero p r s t

/--
[canonicalMaskOrbitCoverageJoinCandidates_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageJoin.lean)
-/
@[path]
private lemma canonicalMaskOrbitCoverageJoinCandidates_nonempty_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r s : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hclosed : CanonicalMaskOrbitCoverageUnionClosed ends m j k l zero p)
  (hrs : CanonicalMaskTransferOrbit ends m j k l zero p r s) :
-- imply
  (canonicalMaskOrbitCoverageJoinCandidates ends m j k l zero p r s).Nonempty := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitCoverageJoinCandidates_nonempty ends m j k l zero p hclosed r s hrs

/--
[canonicalMaskOrbitCoverageJoin_mem_candidates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageJoin.lean)
-/
@[path]
private lemma canonicalMaskOrbitCoverageJoin_mem_candidates_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r s : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hclosed : CanonicalMaskOrbitCoverageUnionClosed ends m j k l zero p)
  (hrs : CanonicalMaskTransferOrbit ends m j k l zero p r s) :
-- imply
  canonicalMaskOrbitCoverageJoin ends m j k l zero p hclosed r s hrs ∈ canonicalMaskOrbitCoverageJoinCandidates ends m j k l zero p r s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitCoverageJoin_mem_candidates ends m j k l zero p hclosed r s hrs

/--
[canonicalMaskOrbitCoverageJoin_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageJoin.lean)
-/
@[path]
private lemma canonicalMaskOrbitCoverageJoin_orbit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r s : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hclosed : CanonicalMaskOrbitCoverageUnionClosed ends m j k l zero p)
  (hrs : CanonicalMaskTransferOrbit ends m j k l zero p r s) :
-- imply
  CanonicalMaskTransferOrbit ends m j k l zero p r (canonicalMaskOrbitCoverageJoin ends m j k l zero p hclosed r s hrs) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitCoverageJoin_orbit ends m j k l zero p hclosed r s hrs

/--
[canonicalMaskOrbitCoverageJoin_works](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageJoin.lean)
-/
@[path]
private lemma canonicalMaskOrbitCoverageJoin_works_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r s : leftMaskFiber ends m j k l zero p}
  {d : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hclosed : CanonicalMaskOrbitCoverageUnionClosed ends m j k l zero p)
  (hrs : CanonicalMaskTransferOrbit ends m j k l zero p r s)
  (hrd : CanonicalMaskTransferOrbit ends m j k l zero p r d)
  (hworks : CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∨ CanonicalTransferWorks ends m k zero s.1.1 d.1.1) :
-- imply
  CanonicalTransferWorks ends m k zero (canonicalMaskOrbitCoverageJoin ends m j k l zero p hclosed r s hrs).1.1 d.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitCoverageJoin_works ends m j k l zero p hclosed r s hrs d hrd hworks

/--
[canonicalMaskOrbitCoverageDirected_of_unionClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageJoin.lean)
-/
@[path]
private lemma canonicalMaskOrbitCoverageDirected_of_unionClosed_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hclosed : CanonicalMaskOrbitCoverageUnionClosed ends m j k l zero p) :
-- imply
  CanonicalMaskOrbitCoverageDirected ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitCoverageDirected_of_unionClosed ends m j k l zero p hclosed

/--
[GrahamFiberMinor_of_canonicalMaskOrbitCoverageUnionClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCoverageJoin.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_canonicalMaskOrbitCoverageUnionClosed_eq
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
  (hclosed : ∀ p : Finset I × Finset I, CanonicalMaskOrbitCoverageUnionClosed ends m j k l zero p) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_canonicalMaskOrbitCoverageUnionClosed ends m j k l zero hloop hjk hkl hk0 hclosed


-- created on 2026-10-23
