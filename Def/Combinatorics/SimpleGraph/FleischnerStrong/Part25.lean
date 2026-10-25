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
import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part12
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
