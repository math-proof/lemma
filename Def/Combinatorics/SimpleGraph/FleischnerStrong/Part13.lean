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
import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part7
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

variable {V : Type*} {G : SimpleGraph V} {x : V}

noncomputable def boundIncidenceEquiv [Finite V] (c : G.Walk x x)
    (hc : c.IsCycle)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    [NeZero c.length]
    (i : Fin c.length) (hbound : c.IsBoundVertex (c.getVert i)) :
    {e : c.TrailSystemEdge cover //
      (c.trailSystemMultigraph cover).Inc (c.getVert i) e} ≃ Fin 2 := by
  let embed : Fin 2 → {e : c.TrailSystemEdge cover //
      (c.trailSystemMultigraph cover).Inc (c.getVert i) e} := fun k ↦
    if hk : k = 0 then
      ⟨Sum.inl (ULift.up i), by
        change c.getVert i ∈ s(c.getVert i, c.getVert (i + 1))
        simp⟩
    else
      ⟨Sum.inl (ULift.up (i - 1)), by
        simp only [EdgeIndexedMultigraph.Inc, trailSystemMultigraph]
        rw [hc.getVert_succ_eq_add_one, sub_add_cancel]
        exact Sym2.mem_iff.mpr (Or.inr rfl)⟩
  have hinj : Function.Injective embed := by
    intro a b hab
    by_cases ha : a = 0
    · subst a
      by_cases hb : b = 0
      · exact hb.symm
      · have hval := congrArg (fun e ↦ e.1) hab
        simp only [embed, dite_eq_left rfl, dite_eq_right hb] at hval
        have hindex : i = i - 1 := by
          simpa only [Sum.inl.injEq, ULift.up_inj] using hval
        exact False.elim (hc.sub_one_ne i hindex.symm)
    · have ha1 : a = 1 := Fin.eq_one_of_ne_zero a ha
      subst a
      by_cases hb : b = 0
      · subst b
        have hval := congrArg (fun e ↦ e.1) hab
        simp only [embed, dite_eq_left rfl,
          dite_eq_right (by decide : (1 : Fin 2) ≠ 0)] at hval
        have hindex : i - 1 = i := by
          simpa only [Sum.inl.injEq, ULift.up_inj] using hval
        exact False.elim (hc.sub_one_ne i hindex)
      · exact (Fin.eq_one_of_ne_zero b hb).symm
  have hsurj : Function.Surjective embed := by
    rintro ⟨e, he⟩
    cases e with
    | inr e =>
        exact False.elim
          (no_cover_inc_bound_vertex c cover i hbound e.1 e.2 he)
    | inl j =>
        change c.getVert i ∈
          s(c.getVert j.down, c.getVert (j.down + 1)) at he
        rcases Sym2.mem_iff.mp he with he | he
        · have hji : j.down = i := hc.getVert_injective_fin he.symm
          refine ⟨0, ?_⟩
          apply Subtype.ext
          change Sum.inl (ULift.up i) = Sum.inl j
          congr
          exact hji.symm
        · rw [hc.getVert_succ_eq_add_one] at he
          have hi : i = j.down + 1 := hc.getVert_injective_fin he
          have hji : j.down = i - 1 := eq_sub_iff_add_eq.mpr hi.symm
          refine ⟨1, ?_⟩
          apply Subtype.ext
          change Sum.inl (ULift.up (i - 1)) = Sum.inl j
          congr
          exact hji.symm
  exact (Equiv.ofBijective embed ⟨hinj, hsurj⟩).symm

noncomputable def cycleCopyIncidenceTo {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) :
    {e : c.CycleCopyEdge q // (c.cycleCopyMultigraph q).Inc (c.getVert i) e} →
      Fin (q.copies (i - 1)) ⊕ Fin (q.copies i) := by
  rintro ⟨⟨j, k⟩, he⟩
  by_cases hji : j = i
  · subst j
    exact Sum.inr k
  · have hjp : j = i - 1 :=
      (cycleCopyMultigraph_inc_getVert_iff hc q i ⟨j, k⟩).mp he |>.resolve_left hji
    subst j
    exact Sum.inl k

def cycleCopyIncidenceFrom {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) :
    Fin (q.copies (i - 1)) ⊕ Fin (q.copies i) →
      {e : c.CycleCopyEdge q // (c.cycleCopyMultigraph q).Inc (c.getVert i) e}
  | Sum.inl k =>
      ⟨⟨i - 1, k⟩, (cycleCopyMultigraph_inc_getVert_iff hc q i _).mpr (Or.inr rfl)⟩
  | Sum.inr k =>
      ⟨⟨i, k⟩, (cycleCopyMultigraph_inc_getVert_iff hc q i _).mpr (Or.inl rfl)⟩

end Walk
end SimpleGraph
