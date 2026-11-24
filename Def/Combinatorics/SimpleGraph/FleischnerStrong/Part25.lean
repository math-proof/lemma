module
public import Def.Combinatorics.SimpleGraph.StrongSquareCycle
public import Theorem.SimpleGraph.StrongSquareCycle
public import Theorem.SimpleGraph.VertexConnectivity
public import Theorem.SimpleGraph.Contraction
public import Theorem.SimpleGraph.EdgeIndexedMultigraph
public import Theorem.SimpleGraph.Riha
public import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
public import Theorem.Combinatorics.SimpleGraph.Contraction.Part3
public import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part4
public import Def.Combinatorics.SimpleGraph.Riha
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Data.List.ChainOfFn
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.ZMod.Basic
public import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part12


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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

/-- Forward forced transitions after deleting the copied closing edge and its original. -/
noncomputable def forwardLastCutCycleTransition (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (hlast : q.copies (cycleLastIndex c.length) = 1) :
    UncutActiveCycleCopy q (lastActiveCycleCopy q hlast) →
      (c.cutAugmentedTrailMultigraph cover q
        (lastActiveCycleCopy q hlast)).EdgeTransition := by
  intro i
  let cut := lastActiveCycleCopy q hlast
  have hi0 := i.1.ne_zero q
  have hiend : i.1.1.val + 1 < c.length := by
    apply fin_val_add_one_lt_of_ne_cycleLastIndex
    simpa [cut, lastActiveCycleCopy] using i.2
  have hpartner : i.1.1 - 1 ≠ cut.1 := by
    intro heq
    have hval := congrArg Fin.val heq
    rw [Fin.val_sub_one_of_ne_zero hi0] at hval
    have hn : 0 < c.length := NeZero.pos c.length
    have hlt := i.1.1.isLt
    change i.1.1.val - 1 = c.length - 1 at hval
    omega
  have hleft :
      (c.cutAugmentedTrailMultigraph cover q cut).ends
          (c.cutOriginalEdge cover q cut (i.1.1 - 1) hpartner) =
        s(c.getVert (i.1.1.val - 1), c.getVert i.1.1.val) := by
    rw [c.cutAugmentedTrailMultigraph_ends_original]
    rw [Fin.val_sub_one_of_ne_zero hi0]
    have hpos : 0 < i.1.1.val :=
      Nat.pos_of_ne_zero (fun h ↦ hi0 (Fin.ext h))
    rw [Nat.sub_add_cancel hpos]
  have hright :
      (c.cutAugmentedTrailMultigraph cover q cut).ends
          (c.cutCopiedEdge cover q cut i) =
        s(c.getVert i.1.1, c.getVert (i.1.1.val + 1)) :=
    c.cutAugmentedTrailMultigraph_ends_copy cover q cut i
  exact {
    left := c.cutOriginalEdge cover q cut (i.1.1 - 1) hpartner
    right := c.cutCopiedEdge cover q cut i
    before := c.getVert (i.1.1.val - 1)
    center := c.getVert i.1.1.val
    after := c.getVert (i.1.1.val + 1)
    left_ends := hleft
    right_ends := hright
    before_ne_after :=
      hc.getVert_sub_one_ne_getVert_add_one (Nat.le_of_lt i.1.1.isLt) }

end Walk
end SimpleGraph
