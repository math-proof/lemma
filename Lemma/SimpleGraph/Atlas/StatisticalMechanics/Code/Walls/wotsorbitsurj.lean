import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.wotsorbitsurj.Part2
open SimpleGraph Function StatMech StatMech.Wots


/--
[wots_dartGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wotsorbitsurj.lean)
-/
@[path]
private lemma wots_dartGraph_adj_eq
  {K : Set (Site 2)}
  {d1 d2 : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (wots_dartGraph K).Adj d1 d2 ↔ d1 ≠ d2 ∧ (KingAdj d1.1.head d2.1.head ∨ d1.1.head = d2.1.head) ∧ ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable ⟨d1.1.head, d1.2.2⟩ ⟨d2.1.head, d2.2.2⟩ := by
-- proof
  apply StatMech.Wots.wots_dartGraph_adj K d1 d2

/--
[wots_reachable_sameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wotsorbitsurj.lean)
-/
@[path]
private lemma wots_reachable_sameOrbit_eq
  {K : Set (Site 2)}
  {d1 d2 : {e : Dart // IsBoundaryDart K e}}
-- given
  (hstep : wots_LocalStepSameOrbit K)
  (h : (wots_dartGraph K).Reachable d1 d2) :
-- imply
  SameOrbit K d1.1 d2.1 := by
-- proof
  apply StatMech.Wots.wots_reachable_sameOrbit K hstep h

/--
[wots_orbitTraceSurjective_of_reduction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wotsorbitsurj.lean)
-/
@[path]
private lemma wots_orbitTraceSurjective_of_reduction_eq
  {K : Set (Site 2)}
-- given
  (hstep : wots_LocalStepSameOrbit K)
  (hconn : wots_DartConnected K) :
-- imply
  OrbitTraceSurjective K := by
-- proof
  apply StatMech.Wots.wots_orbitTraceSurjective_of_reduction K hstep hconn

/--
[wots_localStep_of_orbitTraceSurjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wotsorbitsurj.lean)
-/
@[path]
private lemma wots_localStep_of_orbitTraceSurjective_eq
  {K : Set (Site 2)}
-- given
  (hOTS : OrbitTraceSurjective K) :
-- imply
  wots_LocalStepSameOrbit K := by
-- proof
  apply StatMech.Wots.wots_localStep_of_orbitTraceSurjective K hOTS

/--
[wots_dartNextSub_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wotsorbitsurj.lean)
-/
@[path]
private lemma wots_dartNextSub_adj_eq
  {K : Set (Site 2)}
  {d : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (wots_dartGraph K).Adj d (dartNextSub K d) := by
-- proof
  apply StatMech.Wots.wots_dartNextSub_adj K d

/--
[wots_reachable_of_sameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wotsorbitsurj.lean)
-/
@[path]
private lemma wots_reachable_of_sameOrbit_eq
  {K : Set (Site 2)}
  {d1 d2 : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : SameOrbit K d1.1 d2.1) :
-- imply
  (wots_dartGraph K).Reachable d1 d2 := by
-- proof
  apply StatMech.Wots.wots_reachable_of_sameOrbit K h

/--
[wots_dartConnected_of_orbitTraceSurjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wotsorbitsurj.lean)
-/
@[path]
private lemma wots_dartConnected_of_orbitTraceSurjective_eq
  {K : Set (Site 2)}
-- given
  (hOTS : OrbitTraceSurjective K) :
-- imply
  wots_DartConnected K := by
-- proof
  apply StatMech.Wots.wots_dartConnected_of_orbitTraceSurjective K hOTS

/--
[wots_orbitTraceSurjective_iff_reduction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wotsorbitsurj.lean)
-/
@[path]
private lemma wots_orbitTraceSurjective_iff_reduction_eq
  {K : Set (Site 2)} :
-- imply
  OrbitTraceSurjective K ↔ (wots_LocalStepSameOrbit K ∧ wots_DartConnected K) := by
-- proof
  apply StatMech.Wots.wots_orbitTraceSurjective_iff_reduction K

/--
[wots_interfaceConnected_of_reduction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wotsorbitsurj.lean)
-/
@[path]
private lemma wots_interfaceConnected_of_reduction_eq
  {K : Set (Site 2)}
-- given
  (hstep : wots_LocalStepSameOrbit K)
  (hconn : wots_DartConnected K) :
-- imply
  InterfaceConnected K := by
-- proof
  apply StatMech.Wots.wots_interfaceConnected_of_reduction K hstep hconn

/--
[wots_reduction_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wotsorbitsurj.lean)
-/
@[path]
private lemma wots_reduction_singleton_eq
  {c : Site 2} :
-- imply
  wots_LocalStepSameOrbit ({c} : Set (Site 2)) ∧ wots_DartConnected ({c} : Set (Site 2)) := by
-- proof
  apply StatMech.Wots.wots_reduction_singleton c

/--
[wots_orbitTraceSurjective_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wotsorbitsurj.lean)
-/
@[path]
private lemma wots_orbitTraceSurjective_singleton_eq
  {c : Site 2} :
-- imply
  OrbitTraceSurjective ({c} : Set (Site 2)) := by
-- proof
  apply StatMech.Wots.wots_orbitTraceSurjective_singleton c

/--
[wots_revCount_pm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wotsorbitsurj.lean)
-/
@[path]
private lemma wots_revCount_pm_one_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hpf : WpbPinchFree K a)
  (hstep : wots_LocalStepSameOrbit K)
  (hconn : wots_DartConnected K)
  (hheads : ∀ d : Dart, (hd : IsBoundaryDart K d) → ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨a.1.head, a.2.2⟩ ⟨d.head, hd.2⟩)
  (hbuild : Euc.EucBuildable (wcd_toVtxFinset K hK)) :
-- imply
  revCount K a = 1 ∨ revCount K a = -1 := by
-- proof
  apply StatMech.Wots.wots_revCount_pm_one K hK a hpf hstep hconn hheads hbuild


-- created on 2026-10-23
