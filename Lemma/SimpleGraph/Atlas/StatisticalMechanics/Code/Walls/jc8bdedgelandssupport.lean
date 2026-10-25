import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc8bdedgelandssupport.Part2
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc8_loop_localConstancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8bdedgelandssupport.lean)
-/
@[path]
private lemma jc8_loop_localConstancy_eq
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
  apply StatMech.Walls.jc8_loop_localConstancy K hK e he hadj hu hv

/--
[jc8_bdEdge_lands_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8bdedgelandssupport.lean)
-/
@[path]
private lemma jc8_bdEdge_lands_support_eq
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
  apply StatMech.Walls.jc8_bdEdge_lands_support K hK e he hadj hbd

/--
[jc8_bdEdge_lands_support'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8bdedgelandssupport.lean)
-/
@[path]
private lemma jc8_bdEdge_lands_support'_eq
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
  apply StatMech.Walls.jc8_bdEdge_lands_support' K hK e he hadj hbd

/--
[jc8_bdEdgeLandsSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8bdedgelandssupport.lean)
-/
@[path]
private lemma jc8_bdEdgeLandsSupport_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  jc8_BdEdgeLandsSupport K hK e he := by
-- proof
  apply StatMech.Walls.jc8_bdEdgeLandsSupport K hK e he


-- created on 2026-10-23
