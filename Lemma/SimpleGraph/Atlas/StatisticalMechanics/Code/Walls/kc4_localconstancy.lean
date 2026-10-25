import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc4_localconstancy
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc4_localConstancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_localconstancy.lean)
-/
@[path]
private lemma kc4_localConstancy_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ Vc.support)
  (hv : v ∉ Vc.support) :
-- imply
  (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc)) := by
-- proof
  apply StatMech.Walls.kc4_localConstancy Vc hadj hu hv

/--
[kc4_localConstancy_mod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_localconstancy.lean)
-/
@[path]
private lemma kc4_localConstancy_mod_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ Vc.support)
  (hv : v ∉ Vc.support) :
-- imply
  jec_rayCount u Vc % 2 = jec_rayCount v Vc % 2 := by
-- proof
  apply StatMech.Walls.kc4_localConstancy_mod Vc hadj hu hv

/--
[kc4_memLeftRegion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_localconstancy.lean)
-/
@[path]
private lemma kc4_memLeftRegion_iff_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ Vc.support)
  (hv : v ∉ Vc.support) :
-- imply
  u ∈ jec_leftRegion Vc ↔ v ∈ jec_leftRegion Vc := by
-- proof
  apply StatMech.Walls.kc4_memLeftRegion_iff Vc hadj hu hv

/--
[kc4_parityFlip_imp_onContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_localconstancy.lean)
-/
@[path]
private lemma kc4_parityFlip_imp_onContour_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hflip : ¬ (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc))) :
-- imply
  u ∈ Vc.support ∨ v ∈ Vc.support := by
-- proof
  apply StatMech.Walls.kc4_parityFlip_imp_onContour Vc hadj hflip

/--
[kc4_offContour_pair_noFlip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_localconstancy.lean)
-/
@[path]
private lemma kc4_offContour_pair_noFlip_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  (u ∈ Vc.support ∨ v ∈ Vc.support) ∨ (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc)) := by
-- proof
  apply StatMech.Walls.kc4_offContour_pair_noFlip Vc hadj

/--
[kc4_leftRegion_bdEdge_onContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_localconstancy.lean)
-/
@[path]
private lemma kc4_leftRegion_bdEdge_onContour_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
-- imply
  u ∈ Vc.support ∨ v ∈ Vc.support := by
-- proof
  apply StatMech.Walls.kc4_leftRegion_bdEdge_onContour Vc hadj hbd

/--
[kc4_orbitLoop_localConstancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_localconstancy.lean)
-/
@[path]
private lemma kc4_orbitLoop_localConstancy_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ (mpl_orbitLoop K a).support)
  (hv : v ∉ (mpl_orbitLoop K a).support) :
-- imply
  (Even (jec_rayCount u (mpl_orbitLoop K a)) ↔ Even (jec_rayCount v (mpl_orbitLoop K a))) := by
-- proof
  apply StatMech.Walls.kc4_orbitLoop_localConstancy K a hadj hu hv

/--
[kc4_orbitLoop_localConstancy_mod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_localconstancy.lean)
-/
@[path]
private lemma kc4_orbitLoop_localConstancy_mod_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ (mpl_orbitLoop K a).support)
  (hv : v ∉ (mpl_orbitLoop K a).support) :
-- imply
  jec_rayCount u (mpl_orbitLoop K a) % 2 = jec_rayCount v (mpl_orbitLoop K a) % 2 := by
-- proof
  apply StatMech.Walls.kc4_orbitLoop_localConstancy_mod K a hadj hu hv

/--
[kc4_orbitLoop_memLeftRegion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_localconstancy.lean)
-/
@[path]
private lemma kc4_orbitLoop_memLeftRegion_iff_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ (mpl_orbitLoop K a).support)
  (hv : v ∉ (mpl_orbitLoop K a).support) :
-- imply
  u ∈ jec_leftRegion (mpl_orbitLoop K a) ↔ v ∈ jec_leftRegion (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.kc4_orbitLoop_memLeftRegion_iff K a hadj hu hv

/--
[kc4_orbitLoop_parityFlip_imp_onContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_localconstancy.lean)
-/
@[path]
private lemma kc4_orbitLoop_parityFlip_imp_onContour_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hflip : ¬ (Even (jec_rayCount u (mpl_orbitLoop K a)) ↔ Even (jec_rayCount v (mpl_orbitLoop K a)))) :
-- imply
  u ∈ (mpl_orbitLoop K a).support ∨ v ∈ (mpl_orbitLoop K a).support := by
-- proof
  apply StatMech.Walls.kc4_orbitLoop_parityFlip_imp_onContour K a hadj hflip

/--
[kc4_orbitLoop_leftRegion_bdEdge_onContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_localconstancy.lean)
-/
@[path]
private lemma kc4_orbitLoop_leftRegion_bdEdge_onContour_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion (mpl_orbitLoop K a)) s(u, v)) :
-- imply
  u ∈ (mpl_orbitLoop K a).support ∨ v ∈ (mpl_orbitLoop K a).support := by
-- proof
  apply StatMech.Walls.kc4_orbitLoop_leftRegion_bdEdge_onContour K a hadj hbd

/--
[kc4_supportSet_localConstancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_localconstancy.lean)
-/
@[path]
private lemma kc4_supportSet_localConstancy_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ oc_supportSet (mpl_orbitLoop K a))
  (hv : v ∉ oc_supportSet (mpl_orbitLoop K a)) :
-- imply
  (Even (jec_rayCount u (mpl_orbitLoop K a)) ↔ Even (jec_rayCount v (mpl_orbitLoop K a))) := by
-- proof
  apply StatMech.Walls.kc4_supportSet_localConstancy K a hadj hu hv

/--
[kc4_localConstancy_node](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_localconstancy.lean)
-/
@[path]
private lemma kc4_localConstancy_node_eq :
-- imply
  (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (u v : Site 2), (hypercubicLattice 2).Adj u v → u ∉ Vc.support → v ∉ Vc.support → (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc))) ∧ (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (u v : Site 2), (hypercubicLattice 2).Adj u v → ¬ (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc)) → u ∈ Vc.support ∨ v ∈ Vc.support) ∧ (∀ (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (u v : Site 2), (hypercubicLattice 2).Adj u v → u ∉ (mpl_orbitLoop K a).support → v ∉ (mpl_orbitLoop K a).support → (Even (jec_rayCount u (mpl_orbitLoop K a)) ↔ Even (jec_rayCount v (mpl_orbitLoop K a)))) ∧ (∀ (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (u v : Site 2), (hypercubicLattice 2).Adj u v → ¬ (Even (jec_rayCount u (mpl_orbitLoop K a)) ↔ Even (jec_rayCount v (mpl_orbitLoop K a))) → u ∈ (mpl_orbitLoop K a).support ∨ v ∈ (mpl_orbitLoop K a).support) := by
-- proof
  apply StatMech.Walls.kc4_localConstancy_node

/--
[kc4_unitCell_offContour_localConstancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_localconstancy.lean)
-/
@[path]
private lemma kc4_unitCell_offContour_localConstancy_eq :
-- imply
  ∃ (R : ℕ) (u v : Site 2), ({z | z ∈ (mpl_orbitLoop unitCell ucBase).support} : Set (Site 2)) ⊆ box 2 R ∧ (hypercubicLattice 2).Adj u v ∧ u ∉ (mpl_orbitLoop unitCell ucBase).support ∧ v ∉ (mpl_orbitLoop unitCell ucBase).support ∧ (Even (jec_rayCount u (mpl_orbitLoop unitCell ucBase)) ↔ Even (jec_rayCount v (mpl_orbitLoop unitCell ucBase))) := by
-- proof
  apply StatMech.Walls.kc4_unitCell_offContour_localConstancy


-- created on 2026-10-23
