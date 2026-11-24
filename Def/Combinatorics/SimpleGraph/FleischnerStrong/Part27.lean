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
public import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part14


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

/-- The forced transition associated to every copied edge when neither terminal arc edge is
copied. -/
noncomputable def splitCycleTransition (c : G.Walk x x) (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length] {d : Fin c.length → ℕ} (q : CyclicParityCompletion d)
    (k : Fin c.length) (hlast : q.copies (cycleLastIndex c.length) = 0) :
    ActiveCycleCopy q → (c.augmentedTrailMultigraph cover q).EdgeTransition := by
  intro i
  let partner := splitPartnerIndex k i.1
  by_cases hforward : i.1.val < k.val
  · have hi0 := i.ne_zero q
    have hpartner : partner = i.1 - 1 := by simp [partner, splitPartnerIndex, hforward]
    have hleft :
        (c.augmentedTrailMultigraph cover q).ends
            (c.augmentedOriginalEdge cover q partner) =
          s(c.getVert (i.1.val - 1), c.getVert i.1.val) := by
      rw [hpartner, c.augmentedTrailMultigraph_ends_original]
      rw [Fin.val_sub_one_of_ne_zero hi0]
      have hpos : 0 < i.1.val := Nat.pos_of_ne_zero (by
        intro h
        apply hi0
        apply Fin.ext
        exact h)
      rw [Nat.sub_add_cancel hpos]
    have hright :
        (c.augmentedTrailMultigraph cover q).ends
            (c.augmentedCopiedEdge cover q i.2) =
          s(c.getVert i.1, c.getVert (i.1.val + 1)) :=
      c.augmentedTrailMultigraph_ends_copy cover q i.2
    exact {
      left := c.augmentedOriginalEdge cover q partner
      right := c.augmentedCopiedEdge cover q i.2
      before := c.getVert (i.1.val - 1)
      center := c.getVert i.1.val
      after := c.getVert (i.1.val + 1)
      left_ends := hleft
      right_ends := hright
      before_ne_after := by
        exact hc.getVert_sub_one_ne_getVert_add_one (Nat.le_of_lt i.1.isLt) }
  · have hiend := i.val_add_one_lt q hlast
    have hn2 : 1 < c.length :=
      lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le i.1.val)) hiend
    have hone : (1 : Fin c.length).val = 1 := Nat.mod_eq_of_lt hn2
    have hadd : i.1.val + (1 : Fin c.length).val < c.length := by
      rw [hone]
      exact hiend
    have hpartner : partner = i.1 + 1 := by simp [partner, splitPartnerIndex, hforward]
    have hleft :
        (c.augmentedTrailMultigraph cover q).ends
            (c.augmentedOriginalEdge cover q partner) =
          s(c.getVert (i.1.val + 2), c.getVert (i.1.val + 1)) := by
      rw [hpartner, c.augmentedTrailMultigraph_ends_original,
        Fin.val_add_eq_of_add_lt hadd, hone]
      exact Sym2.eq_swap
    have hright :
        (c.augmentedTrailMultigraph cover q).ends
            (c.augmentedCopiedEdge cover q i.2) =
          s(c.getVert (i.1.val + 1), c.getVert i.1.val) := by
      rw [c.augmentedTrailMultigraph_ends_copy, Sym2.eq_swap]
    exact {
      left := c.augmentedOriginalEdge cover q partner
      right := c.augmentedCopiedEdge cover q i.2
      before := c.getVert (i.1.val + 2)
      center := c.getVert (i.1.val + 1)
      after := c.getVert i.1.val
      left_ends := hleft
      right_ends := hright
      before_ne_after := by
        have hne := hc.getVert_sub_one_ne_getVert_add_one
          (i := i.1.val + 1) (by omega : i.1.val + 1 ≤ c.length)
        simpa using hne.symm }

end Walk
end SimpleGraph
