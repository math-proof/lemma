import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc10localconstancy
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[jc10_loop_ray_wall_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10localconstancy.lean)
-/
@[path]
private lemma jc10_loop_ray_wall_parity_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  Even (jec_rayCount z Vc) ↔ Even (jec_wallCount z Vc) := by
-- proof
  apply StatMech.Walls.jc10_loop_ray_wall_parity z Vc

/--
[jc10_localConstancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10localconstancy.lean)
-/
@[path]
private lemma jc10_localConstancy_eq
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
  apply StatMech.Walls.jc10_localConstancy Vc hadj hu hv

/--
[jc10_localConstancy_eq_jec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10localconstancy.lean)
-/
@[path]
private lemma jc10_localConstancy_eq_jec_eq
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
  apply StatMech.Walls.jc10_localConstancy_eq_jec Vc hadj hu hv

/--
[jc10_leftRegion_bdEdge_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10localconstancy.lean)
-/
@[path]
private lemma jc10_leftRegion_bdEdge_support_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
-- imply
  u ∈ Vc.support ∨ v ∈ Vc.support := by
-- proof
  apply StatMech.Walls.jc10_leftRegion_bdEdge_support Vc hadj hbd

/--
[jc10_mpl_localConstancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10localconstancy.lean)
-/
@[path]
private lemma jc10_mpl_localConstancy_eq
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
  apply StatMech.Walls.jc10_mpl_localConstancy K a hadj hu hv

/--
[jc10_olb_localConstancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10localconstancy.lean)
-/
@[path]
private lemma jc10_olb_localConstancy_eq
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
  apply StatMech.Walls.jc10_olb_localConstancy K hK e he hadj hu hv


-- created on 2026-10-23
