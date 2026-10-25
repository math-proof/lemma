import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc6localconstancy
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc6_loop_ray_wall_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6localconstancy.lean)
-/
@[path]
private lemma kc6_loop_ray_wall_parity_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  Even (jec_rayCount z Vc) ↔ Even (jec_wallCount z Vc) := by
-- proof
  apply StatMech.Walls.kc6_loop_ray_wall_parity z Vc

/--
[kc6_localConstancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6localconstancy.lean)
-/
@[path]
private lemma kc6_localConstancy_eq
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
  apply StatMech.Walls.kc6_localConstancy Vc hadj hu hv

/--
[kc6_localConstancy_mod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6localconstancy.lean)
-/
@[path]
private lemma kc6_localConstancy_mod_eq
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
  apply StatMech.Walls.kc6_localConstancy_mod Vc hadj hu hv

/--
[kc6_memLeftRegion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6localconstancy.lean)
-/
@[path]
private lemma kc6_memLeftRegion_iff_eq
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
  apply StatMech.Walls.kc6_memLeftRegion_iff Vc hadj hu hv

/--
[kc6_parityFlip_imp_onContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6localconstancy.lean)
-/
@[path]
private lemma kc6_parityFlip_imp_onContour_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hflip : ¬ (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc))) :
-- imply
  u ∈ Vc.support ∨ v ∈ Vc.support := by
-- proof
  apply StatMech.Walls.kc6_parityFlip_imp_onContour Vc hadj hflip

/--
[kc6_leftRegion_bdEdge_onSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6localconstancy.lean)
-/
@[path]
private lemma kc6_leftRegion_bdEdge_onSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
-- imply
  u ∈ Vc.support ∨ v ∈ Vc.support := by
-- proof
  apply StatMech.Walls.kc6_leftRegion_bdEdge_onSupport Vc hadj hbd

/--
[kc6_leftRegion_bdEdge_onSupport_eq_jec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6localconstancy.lean)
-/
@[path]
private lemma kc6_leftRegion_bdEdge_onSupport_eq_jec_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
-- imply
  u ∈ Vc.support ∨ v ∈ Vc.support := by
-- proof
  apply StatMech.Walls.kc6_leftRegion_bdEdge_onSupport_eq_jec Vc hadj hbd

/--
[kc6_mpl_localConstancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6localconstancy.lean)
-/
@[path]
private lemma kc6_mpl_localConstancy_eq
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
  apply StatMech.Walls.kc6_mpl_localConstancy K a hadj hu hv

/--
[kc6_mpl_memLeftRegion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6localconstancy.lean)
-/
@[path]
private lemma kc6_mpl_memLeftRegion_iff_eq
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
  apply StatMech.Walls.kc6_mpl_memLeftRegion_iff K a hadj hu hv

/--
[kc6_mpl_leftRegion_bdEdge_onSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6localconstancy.lean)
-/
@[path]
private lemma kc6_mpl_leftRegion_bdEdge_onSupport_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion (mpl_orbitLoop K a)) s(u, v)) :
-- imply
  u ∈ (mpl_orbitLoop K a).support ∨ v ∈ (mpl_orbitLoop K a).support := by
-- proof
  apply StatMech.Walls.kc6_mpl_leftRegion_bdEdge_onSupport K a hadj hbd

/--
[kc6_olb_localConstancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6localconstancy.lean)
-/
@[path]
private lemma kc6_olb_localConstancy_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ (olb_orbitLoop K hK e he).support)
  (hv : v ∉ (olb_orbitLoop K hK e he).support) :
-- imply
  (Even (jec_rayCount u (olb_orbitLoop K hK e he)) ↔ Even (jec_rayCount v (olb_orbitLoop K hK e he))) := by
-- proof
  apply StatMech.Walls.kc6_olb_localConstancy K hK e he hadj hu hv

/--
[kc6_olb_leftRegion_bdEdge_onSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6localconstancy.lean)
-/
@[path]
private lemma kc6_olb_leftRegion_bdEdge_onSupport_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v)) :
-- imply
  u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support := by
-- proof
  apply StatMech.Walls.kc6_olb_leftRegion_bdEdge_onSupport K hK e he hadj hbd

/--
[kc6_localConstancy_node](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6localconstancy.lean)
-/
@[path]
private lemma kc6_localConstancy_node_eq :
-- imply
  (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (u v : Site 2), (hypercubicLattice 2).Adj u v → u ∉ Vc.support → v ∉ Vc.support → (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc))) ∧ (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (u v : Site 2), (hypercubicLattice 2).Adj u v → bdEdge (jec_leftRegion Vc) s(u, v) → u ∈ Vc.support ∨ v ∈ Vc.support) ∧ (∀ (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (u v : Site 2), (hypercubicLattice 2).Adj u v → u ∉ (mpl_orbitLoop K a).support → v ∉ (mpl_orbitLoop K a).support → (Even (jec_rayCount u (mpl_orbitLoop K a)) ↔ Even (jec_rayCount v (mpl_orbitLoop K a)))) ∧ (∀ (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (u v : Site 2), (hypercubicLattice 2).Adj u v → bdEdge (jec_leftRegion (mpl_orbitLoop K a)) s(u, v) → u ∈ (mpl_orbitLoop K a).support ∨ v ∈ (mpl_orbitLoop K a).support) ∧ (∀ (K : Set (Site 2)) (hK : K.Finite) (e : Dart) (he : IsBoundaryDart K e) (u v : Site 2), (hypercubicLattice 2).Adj u v → u ∉ (olb_orbitLoop K hK e he).support → v ∉ (olb_orbitLoop K hK e he).support → (Even (jec_rayCount u (olb_orbitLoop K hK e he)) ↔ Even (jec_rayCount v (olb_orbitLoop K hK e he)))) ∧ (∀ (K : Set (Site 2)) (hK : K.Finite) (e : Dart) (he : IsBoundaryDart K e) (u v : Site 2), (hypercubicLattice 2).Adj u v → bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v) → u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support) := by
-- proof
  apply StatMech.Walls.kc6_localConstancy_node

/--
[kc6_unitCell_offSupport_localConstancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6localconstancy.lean)
-/
@[path]
private lemma kc6_unitCell_offSupport_localConstancy_eq :
-- imply
  ∃ (R : ℕ) (u v : Site 2), ({z | z ∈ (mpl_orbitLoop unitCell ucBase).support} : Set (Site 2)) ⊆ box 2 R ∧ (hypercubicLattice 2).Adj u v ∧ u ∉ (mpl_orbitLoop unitCell ucBase).support ∧ v ∉ (mpl_orbitLoop unitCell ucBase).support ∧ (Even (jec_rayCount u (mpl_orbitLoop unitCell ucBase)) ↔ Even (jec_rayCount v (mpl_orbitLoop unitCell ucBase))) := by
-- proof
  apply StatMech.Walls.kc6_unitCell_offSupport_localConstancy


-- created on 2026-10-23
