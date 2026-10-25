/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Def.Combinatorics.SimpleGraph.StrongSquareCycle
import Lemma.SimpleGraph.StrongSquareCycle
import Lemma.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.Contraction
import Lemma.SimpleGraph.EdgeIndexedMultigraph
import Lemma.SimpleGraph.Riha
import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
import Theorem.Combinatorics.SimpleGraph.Contraction.Part3
import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part4
import Def.Combinatorics.SimpleGraph.Riha
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Basic.Finite.Sigma
import Mathlib.Basic.Finite.Sum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.ZMod.Basic
import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part5
/-!
# The strengthened Fleischner theorem

This file proves the vertex-rooted form of Fleischner's theorem: the square has a Hamiltonian
cycle whose two edges at a prescribed vertex are edges of the original graph.

The proof-specific component, trail, transition, Euler-circuit, and marking constructions are
private to this module.
-/

/-! ## CycleComplement -/


namespace SimpleGraph

namespace Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {x : V}

def componentIncidenceToTrailSystem (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    {v : V} (hv : v ∉ c.support) :
    {e : (cover (outsideComponent c hv)).Edge |
      (cover (outsideComponent c hv)).multigraph.Inc v e} →
      {e : c.TrailSystemEdge cover | (c.trailSystemMultigraph cover).Inc v e} :=
  fun e ↦ ⟨Sum.inr ⟨outsideComponent c hv, e.1⟩, e.2⟩

noncomputable def trailSystemIncidenceToComponent (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    {v : V} (hv : v ∉ c.support) :
    {e : c.TrailSystemEdge cover | (c.trailSystemMultigraph cover).Inc v e} →
      {e : (cover (outsideComponent c hv)).Edge |
        (cover (outsideComponent c hv)).multigraph.Inc v e} := by
  rintro ⟨e, hve⟩
  cases e with
  | inl i =>
      exfalso
      exact hv (mem_support_of_mem_cycle_edge c i.down hve)
  | inr e =>
      rcases e with ⟨D, e⟩
      have hvD : v ∈ c.componentVertices D := by
        rcases (cover D).endpoints_mem e v hve with hvD | hvc
        · exact hvD
        · exact False.elim (hv hvc)
      have hD := component_eq_outsideComponent c D hv hvD
      subst D
      exact ⟨e, hve⟩

noncomputable def trailSystemIncidenceEquiv (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    {v : V} (hv : v ∉ c.support) :
    {e : (cover (outsideComponent c hv)).Edge |
      (cover (outsideComponent c hv)).multigraph.Inc v e} ≃
      {e : c.TrailSystemEdge cover | (c.trailSystemMultigraph cover).Inc v e} where
  toFun := componentIncidenceToTrailSystem c cover hv
  invFun := trailSystemIncidenceToComponent c cover hv
  left_inv := by
    intro e
    apply Subtype.ext
    simp [componentIncidenceToTrailSystem, trailSystemIncidenceToComponent]
  right_inv := by
    rintro ⟨e, he⟩
    apply Subtype.ext
    cases e with
    | inl i => exact False.elim (hv (mem_support_of_mem_cycle_edge c i.down he))
    | inr e =>
        rcases e with ⟨D, e⟩
        have hvD : v ∈ c.componentVertices D := by
          rcases (cover D).endpoints_mem e v he with hvD | hvc
          · exact hvD
          · exact False.elim (hv hvc)
        have hD := component_eq_outsideComponent c D hv hvD
        subst D
        rfl

end Walk
end SimpleGraph
