import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
open Finset Set SimpleGraph StatMech StatMech.Lattice StatMech.Lattice.EulerianExistence


/--
[degree_eq_card_filter_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma degree_eq_card_filter_edges_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V} :
-- imply
  G.degree x = (G.edgeFinset.filter (fun e => x ∈ e)).card := by
-- proof
  apply StatMech.Lattice.EulerianExistence.degree_eq_card_filter_edges G x

/--
[edgeFinset_deleteEdges_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma edgeFinset_deleteEdges_finset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset (Sym2 V)} :
-- imply
  (G.deleteEdges (S : Set (Sym2 V))).edgeFinset = G.edgeFinset \ S := by
-- proof
  apply StatMech.Lattice.EulerianExistence.edgeFinset_deleteEdges_finset G S

/--
[even_degree_deleteEdges_closedTrail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma even_degree_deleteEdges_closedTrail_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u : V}
  {p : G.Walk u u}
  {x : V}
-- given
  (hp : p.IsTrail)
  (hx : Even (G.degree x)) :
-- imply
  Even ((G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).degree x) := by
-- proof
  apply StatMech.Lattice.EulerianExistence.even_degree_deleteEdges_closedTrail G hp x hx

/--
[exists_maximal_closed_trail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma exists_maximal_closed_trail_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u : V} :
-- imply
  ∃ p : G.Walk u u, p.IsTrail ∧ ∀ q : G.Walk u u, q.IsTrail → q.length ≤ p.length := by
-- proof
  apply StatMech.Lattice.EulerianExistence.exists_maximal_closed_trail G u

/--
[spliceWalk_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma spliceWalk_length_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {u w : V}
  {p : G.Walk u u}
  {c : G.Walk w w}
-- given
  (hw : w ∈ p.support) :
-- imply
  (spliceWalk G p hw c).length = p.length + c.length := by
-- proof
  apply StatMech.Lattice.EulerianExistence.spliceWalk_length G p hw c

/--
[spliceWalk_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma spliceWalk_edges_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {u w : V}
  {p : G.Walk u u}
  {c : G.Walk w w}
-- given
  (hw : w ∈ p.support) :
-- imply
  (spliceWalk G p hw c).edges = (p.takeUntil w hw).edges ++ (c.edges ++ (p.dropUntil w hw).edges) := by
-- proof
  apply StatMech.Lattice.EulerianExistence.spliceWalk_edges G p hw c

/--
[spliceWalk_isTrail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma spliceWalk_isTrail_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {u w : V}
  {p : G.Walk u u}
  {c : G.Walk w w}
-- given
  (hp : p.IsTrail)
  (hw : w ∈ p.support)
  (hc : c.IsTrail)
  (hdisj : ∀ e ∈ c.edges, e ∉ p.edges) :
-- imply
  (spliceWalk G p hw c).IsTrail := by
-- proof
  apply StatMech.Lattice.EulerianExistence.spliceWalk_isTrail G hp hw hc hdisj

/--
[exists_boundary_edge_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma exists_boundary_edge_of_walk_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A : Set V} :
-- imply
  ∀ {a b : V} (q : G.Walk a b), a ∈ A → b ∉ A → ∃ c d : V, G.Adj c d ∧ c ∈ A ∧ d ∉ A ∧ s(c, d) ∈ q.edges := by
-- proof
  apply StatMech.Lattice.EulerianExistence.exists_boundary_edge_of_walk G

/--
[exists_closed_eulerian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma exists_closed_eulerian_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u : V}
-- given
  (hconn : G.Connected)
  (heven : ∀ x, Even (G.degree x)) :
-- imply
  ∃ p : G.Walk u u, p.IsTrail ∧ ∀ e ∈ G.edgeFinset, e ∈ p.edges := by
-- proof
  apply StatMech.Lattice.EulerianExistence.exists_closed_eulerian G hconn heven u

/--
[closed_eulerian_length_eq_edgeFinset_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma closed_eulerian_length_eq_edgeFinset_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u : V}
  {p : G.Walk u u}
-- given
  (hp : p.IsTrail)
  (hcov : ∀ e ∈ G.edgeFinset, e ∈ p.edges) :
-- imply
  p.length = G.edgeFinset.card := by
-- proof
  apply StatMech.Lattice.EulerianExistence.closed_eulerian_length_eq_edgeFinset_card G hp hcov

/--
[exists_closed_eulerian_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma exists_closed_eulerian_length_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u : V}
-- given
  (hconn : G.Connected)
  (heven : ∀ x, Even (G.degree x)) :
-- imply
  ∃ p : G.Walk u u, p.IsTrail ∧ (∀ e ∈ G.edgeFinset, e ∈ p.edges) ∧ p.length = G.edgeFinset.card := by
-- proof
  apply StatMech.Lattice.EulerianExistence.exists_closed_eulerian_length G hconn heven u

/--
[exists_closed_eulerian_of_finite_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma exists_closed_eulerian_of_finite_support_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  [LocallyFinite G]
  {T : Finset V}
  {u : V}
-- given
  (hsupp : G.support ⊆ (T : Set V))
  (hconn : (G.induce (T : Set V)).Connected)
  (heven : ∀ x, Even (G.degree x))
  (huT : u ∈ (T : Set V)) :
-- imply
  ∃ p : G.Walk u u, p.IsTrail ∧ ∀ e ∈ G.edgeSet, e ∈ p.edges := by
-- proof
  apply StatMech.Lattice.EulerianExistence.exists_closed_eulerian_of_finite_support G T hsupp hconn heven huT

/--
[faceBoundaryGraph_single_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma faceBoundaryGraph_single_dualCircuit_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
  {f₀ : Site 2}
-- given
  (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
  (hconn : FaceBoundaryConnected K T)
  (hf₀ : f₀ ∈ (T : Set (Site 2))) :
-- imply
  ∃ c : (faceBoundaryGraph K).Walk f₀ f₀, c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges := by
-- proof
  apply StatMech.Lattice.faceBoundaryGraph_single_dualCircuit hsupp hconn hf₀

/--
[boundarySupport_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma boundarySupport_spec_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  (faceBoundaryGraph K).support ⊆ (boundarySupport hK : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.boundarySupport_spec hK

/--
[exists_single_dualCircuit_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma exists_single_dualCircuit_of_connected_eq
  {K : Set (Site 2)}
  {f₀ : Site 2}
-- given
  (hK : K.Finite)
  (hconn : FaceBoundaryConnected K (boundarySupport hK))
  (hf₀ : f₀ ∈ (boundarySupport hK : Set (Site 2))) :
-- imply
  ∃ c : (faceBoundaryGraph K).Walk f₀ f₀, c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges := by
-- proof
  apply StatMech.Lattice.exists_single_dualCircuit_of_connected hK hconn hf₀

/--
[faceBoundaryConnected_satisfiable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma faceBoundaryConnected_satisfiable_iff_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)} :
-- imply
  FaceBoundaryConnected K T ↔ ((faceBoundaryGraph K).induce (T : Set (Site 2))).Connected := by
-- proof
  apply StatMech.Lattice.faceBoundaryConnected_satisfiable_iff

/--
[triangle_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma triangle_connected_eq :
-- imply
  (completeGraph (Fin 3)).Connected := by
-- proof
  apply StatMech.Lattice.triangle_connected

/--
[triangle_even_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma triangle_even_degree_eq
  {v : Fin 3} :
-- imply
  Even ((completeGraph (Fin 3)).degree v) := by
-- proof
  apply StatMech.Lattice.triangle_even_degree v

/--
[triangle_eulerian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma triangle_eulerian_eq :
-- imply
  ∃ p : (completeGraph (Fin 3)).Walk 0 0, p.IsTrail ∧ (∀ e ∈ (completeGraph (Fin 3)).edgeFinset, e ∈ p.edges) ∧ p.length = (completeGraph (Fin 3)).edgeFinset.card := by
-- proof
  apply StatMech.Lattice.triangle_eulerian

/--
[triangle_edge_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean)
-/
@[path]
private lemma triangle_edge_card_eq :
-- imply
  (completeGraph (Fin 3)).edgeFinset.card = 3 := by
-- proof
  apply StatMech.Lattice.triangle_edge_card


-- created on 2026-10-23
