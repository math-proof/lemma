import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc12core.Part3
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc12_farLeftBeacon_mem_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean)
-/
@[path]
private lemma kc12_farLeftBeacon_mem_exterior_eq
  {a : Site 2}
  {R : ℕ} :
-- imply
  (![-((R : ℤ) + 1), 0] : Site 2) ∈ exterior 2 R := by
-- proof
  apply StatMech.Walls.kc12_farLeftBeacon_mem_exterior R

/--
[kc12_far_mem_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean)
-/
@[path]
private lemma kc12_far_mem_exterior_eq
  {a : Site 2}
  {R : ℕ}
  {w : Site 2}
-- given
  (hw : w 0 ≤ -((R : ℤ) + 1)) :
-- imply
  w ∈ exterior 2 R := by
-- proof
  apply StatMech.Walls.kc12_far_mem_exterior R hw

/--
[kc12_offSupportReaches_of_reachesFarLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean)
-/
@[path]
private lemma kc12_offSupportReaches_of_reachesFarLeft_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hres : kc12_ReachesFarLeftBeacon Vc R) :
-- imply
  kc5_OffSupportReachesExterior Vc R := by
-- proof
  apply StatMech.Walls.kc12_offSupportReaches_of_reachesFarLeft Vc R hres

/--
[kc12_exterior_reaches_farLeftBeacon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean)
-/
@[path]
private lemma kc12_exterior_reaches_farLeftBeacon_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {e : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (heExt : e ∈ exterior 2 R) :
-- imply
  ∃ p : (hypercubicLattice 2).Walk e ![-((R : ℤ) + 1), 0], ∀ u ∈ p.support, u ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc12_exterior_reaches_farLeftBeacon Vc R hsupp heExt

/--
[kc12_reachesFarLeftBeacon_of_offSupportReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean)
-/
@[path]
private lemma kc12_reachesFarLeftBeacon_of_offSupportReaches_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (htgt : kc5_OffSupportReachesExterior Vc R) :
-- imply
  kc12_ReachesFarLeftBeacon Vc R := by
-- proof
  apply StatMech.Walls.kc12_reachesFarLeftBeacon_of_offSupportReaches Vc R hsupp htgt

/--
[kc12_reachesFarLeftBeacon_iff_offSupportReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean)
-/
@[path]
private lemma kc12_reachesFarLeftBeacon_iff_offSupportReaches_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R) :
-- imply
  kc12_ReachesFarLeftBeacon Vc R ↔ kc5_OffSupportReachesExterior Vc R := by
-- proof
  apply StatMech.Walls.kc12_reachesFarLeftBeacon_iff_offSupportReaches Vc R hsupp

/--
[kc12_outsideOffSupportInfinite_of_reachesFarLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean)
-/
@[path]
private lemma kc12_outsideOffSupportInfinite_of_reachesFarLeft_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hres : kc12_ReachesFarLeftBeacon Vc R) :
-- imply
  kc5_OutsideOffSupportInfinite Vc := by
-- proof
  apply StatMech.Walls.kc12_outsideOffSupportInfinite_of_reachesFarLeft Vc R hsupp hres

/--
[kc12_reachesFarLeftBeacon_iff_outsideOffSupportInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean)
-/
@[path]
private lemma kc12_reachesFarLeftBeacon_iff_outsideOffSupportInfinite_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R) :
-- imply
  kc12_ReachesFarLeftBeacon Vc R ↔ kc5_OutsideOffSupportInfinite Vc := by
-- proof
  apply StatMech.Walls.kc12_reachesFarLeftBeacon_iff_outsideOffSupportInfinite Vc R hsupp

/--
[kc12_offSupport_reachable_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean)
-/
@[path]
private lemma kc12_offSupport_reachable_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z w : Site 2}
-- given
  (hz : z ∉ Vc.support)
  (h : (offSupport Vc).Reachable z w) :
-- imply
  w ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc12_offSupport_reachable_offSupport Vc hz h

/--
[kc12_finiteComponent_top_blocked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean)
-/
@[path]
private lemma kc12_finiteComponent_top_blocked_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : z ∉ Vc.support)
  (hfin : (kc12_component Vc z).Finite) :
-- imply
  ∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0, w 1 + 1] : Site 2) ∈ Vc.support := by
-- proof
  apply StatMech.Walls.kc12_finiteComponent_top_blocked Vc hz hfin

/--
[kc12_finiteComponent_bottom_blocked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean)
-/
@[path]
private lemma kc12_finiteComponent_bottom_blocked_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : z ∉ Vc.support)
  (hfin : (kc12_component Vc z).Finite) :
-- imply
  ∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0, w 1 - 1] : Site 2) ∈ Vc.support := by
-- proof
  apply StatMech.Walls.kc12_finiteComponent_bottom_blocked Vc hz hfin

/--
[kc12_finiteComponent_right_blocked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean)
-/
@[path]
private lemma kc12_finiteComponent_right_blocked_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : z ∉ Vc.support)
  (hfin : (kc12_component Vc z).Finite) :
-- imply
  ∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0 + 1, w 1] : Site 2) ∈ Vc.support := by
-- proof
  apply StatMech.Walls.kc12_finiteComponent_right_blocked Vc hz hfin

/--
[kc12_finiteComponent_left_blocked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean)
-/
@[path]
private lemma kc12_finiteComponent_left_blocked_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : z ∉ Vc.support)
  (hfin : (kc12_component Vc z).Finite) :
-- imply
  ∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0 - 1, w 1] : Site 2) ∈ Vc.support := by
-- proof
  apply StatMech.Walls.kc12_finiteComponent_left_blocked Vc hz hfin

/--
[kc12_finiteComponent_enclosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean)
-/
@[path]
private lemma kc12_finiteComponent_enclosed_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : z ∉ Vc.support)
  (hfin : (kc12_component Vc z).Finite) :
-- imply
  (∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0, w 1 + 1] : Site 2) ∈ Vc.support) ∧ (∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0, w 1 - 1] : Site 2) ∈ Vc.support) ∧ (∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0 + 1, w 1] : Site 2) ∈ Vc.support) ∧ (∃ w : Site 2, (offSupport Vc).Reachable z w ∧ (![w 0 - 1, w 1] : Site 2) ∈ Vc.support) := by
-- proof
  apply StatMech.Walls.kc12_finiteComponent_enclosed Vc hz hfin

/--
[kc12_offSupportOutsideInfinite_of_reachesFarLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean)
-/
@[path]
private lemma kc12_offSupportOutsideInfinite_of_reachesFarLeft_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hbridge : kc6_OffSupportOutsideInK K a)
  (hres : kc12_ReachesFarLeftBeacon (mpl_orbitLoop K a) R) :
-- imply
  kc7_OffSupportOutsideInfinite K a := by
-- proof
  apply StatMech.Walls.kc12_offSupportOutsideInfinite_of_reachesFarLeft K a R hRbox hbridge hres

/--
[kc12_unitCell_reachesFarLeftBeacon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean)
-/
@[path]
private lemma kc12_unitCell_reachesFarLeftBeacon_eq
  {a : Site 2} :
-- imply
  kc12_ReachesFarLeftBeacon (mpl_orbitLoop unitCell ucBase) 1 := by
-- proof
  apply StatMech.Walls.kc12_unitCell_reachesFarLeftBeacon

/--
[kc12_unitCell_offSupportReaches_via_farLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean)
-/
@[path]
private lemma kc12_unitCell_offSupportReaches_via_farLeft_eq
  {a : Site 2} :
-- imply
  kc5_OffSupportReachesExterior (mpl_orbitLoop unitCell ucBase) 1 := by
-- proof
  apply StatMech.Walls.kc12_unitCell_offSupportReaches_via_farLeft


-- created on 2026-10-23
