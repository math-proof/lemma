import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.pcffaceclose
open Finset Set SimpleGraph StatMech StatMech.Walls


/--
[pcf_faceCutGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pcffaceclose.lean)
-/
@[path]
private lemma pcf_faceCutGraph_adj_eq
  {f g : Site 2}
-- given
  (T : Site 2 → Prop) :
-- imply
  (pcf_faceCutGraph T).Adj f g ↔ (hypercubicLattice 2).Adj f g ∧ (T f ↔ ¬ T g) := by
-- proof
  apply StatMech.Walls.pcf_faceCutGraph_adj T f g

/--
[pcf_faceCutGraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pcffaceclose.lean)
-/
@[path]
private lemma pcf_faceCutGraph_le_eq
-- given
  (T : Site 2 → Prop) :
-- imply
  pcf_faceCutGraph T ≤ hypercubicLattice 2 := by
-- proof
  apply StatMech.Walls.pcf_faceCutGraph_le T

/--
[pcf_neighborFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pcffaceclose.lean)
-/
@[path]
private lemma pcf_neighborFinset_eq
  {f : Site 2}
-- given
  (T : Site 2 → Prop) :
-- imply
  (pcf_faceCutGraph T).neighborFinset f = (candFinset 2 f).filter (fun g => (pcf_faceCutGraph T).Adj f g) := by
-- proof
  apply StatMech.Walls.pcf_neighborFinset T f

/--
[pcf_faceCutGraph_edge_iff_cutSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pcffaceclose.lean)
-/
@[path]
private lemma pcf_faceCutGraph_edge_iff_cutSet_eq
  {f g : Site 2}
-- given
  (T : Site 2 → Prop)
  (hfg : (hypercubicLattice 2).Adj f g) :
-- imply
  (pcf_faceCutGraph T).Adj f g ↔ sharedPrimalEdge f g ∈ jed_cutSet T := by
-- proof
  apply StatMech.Walls.pcf_faceCutGraph_edge_iff_cutSet T hfg

/--
[pcf_faceCutGraph_of_simpleCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pcffaceclose.lean)
-/
@[path]
private lemma pcf_faceCutGraph_of_simpleCycle_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {f g : Site 2}
-- given
  (hnd : Vc.edges.Nodup)
  (hfg : (hypercubicLattice 2).Adj f g) :
-- imply
  (pcf_faceCutGraph (fwr_faceInside Vc)).Adj f g ↔ sharedPrimalEdge f g ∈ Vc.edges := by
-- proof
  apply StatMech.Walls.pcf_faceCutGraph_of_simpleCycle Vc hnd hfg

/--
[pcf_faceCutGraph_face_degree_not_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pcffaceclose.lean)
-/
@[path]
private lemma pcf_faceCutGraph_face_degree_not_even_eq :
-- imply
  ¬ (∀ (T : Site 2 → Prop) (f : Site 2), Even ((pcf_faceCutGraph T).degree f)) := by
-- proof
  apply StatMech.Walls.pcf_faceCutGraph_face_degree_not_even

/--
[pcf_evenDegree_not_connectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pcffaceclose.lean)
-/
@[path]
private lemma pcf_evenDegree_not_connectivity_eq :
-- imply
  ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj), (∀ v, Even (G.degree v)) ∧ ¬ G.Connected := by
-- proof
  apply StatMech.Walls.pcf_evenDegree_not_connectivity

/--
[pcf_single_dualCircuit_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pcffaceclose.lean)
-/
@[path]
private lemma pcf_single_dualCircuit_of_connected_eq
  {K : Set (Site 2)}
  {f₀ : Site 2}
-- given
  (hK : K.Finite)
  (hconn : FaceBoundaryConnected K (boundarySupport hK))
  (hf₀ : f₀ ∈ (boundarySupport hK : Set (Site 2))) :
-- imply
  ∃ c : (faceBoundaryGraph K).Walk f₀ f₀, c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges := by
-- proof
  apply StatMech.Walls.pcf_single_dualCircuit_of_connected hK hconn hf₀


-- created on 2026-10-23
