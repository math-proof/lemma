/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part28
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectStripRowCast_injective {W n : Nat} :
    Function.Injective (fkRectStripRowCast (W := W) (n := n)) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  simp only [fkRectStripRowCast, Prod.mk.injEq] at h ⊢
  exact ⟨h.1, Fin.castSucc_inj.mp h.2⟩

theorem sym2_fkRectStripRowCast_ne_cast_last
    {W n : Nat} (e : Sym2 (Fin W × Fin (n + 1)))
    (z : Fin W × Fin (n + 1)) (x : Fin W) :
    Sym2.map fkRectStripRowCast e ≠
      s(fkRectStripRowCast z, (x, Fin.last (n + 1))) := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    rw [Sym2.map_pair_eq]
    intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with h | h
    · exact Fin.castSucc_ne_last _ (congrArg Prod.snd h.2)
    · exact Fin.castSucc_ne_last _ (congrArg Prod.snd h.1)

theorem sym2_fkRectStripRowCast_ne_last_last
    {W n : Nat} (e : Sym2 (Fin W × Fin (n + 1))) (x y : Fin W) :
    Sym2.map fkRectStripRowCast e ≠
      s((x, Fin.last (n + 1)), (y, Fin.last (n + 1))) := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    rw [Sym2.map_pair_eq]
    intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with h | h
    · exact Fin.castSucc_ne_last _ (congrArg Prod.snd h.1)
    · exact Fin.castSucc_ne_last _ (congrArg Prod.snd h.1)


theorem fkRectStripGraph_adj_iff_coordinateEdge
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
    (u v : FKRectStripVertex W n) :
    (fkRectStripGraph hW n layers).Adj u v ↔
      u ≠ v ∧ ∃ i : Fin n, ∃ a : Bool × Fin W,
        (layers i).2 a = true ∧
          fkRectCoordinateLayerEdge hW i (layers i).1 a =
            s(fkRectStripVertexEquiv W n u,
              fkRectStripVertexEquiv W n v) := by
  induction n with
  | zero => simp [fkRectStripGraph]
  | succ n ih =>
      let priorLayers : Fin n -> Bool × (Bool × Fin W -> Bool) :=
        fun i => layers i.castSucc
      let rowCast : Fin W × Fin (n + 1) -> Fin W × Fin (n + 2) :=
        fkRectStripRowCast
      have hrowCast : Function.Injective rowCast :=
        fkRectStripRowCast_injective
      constructor
      · intro hadj
        have hne : u ≠ v := fun huv =>
          (fkRectStripGraph hW (n + 1) layers).loopless.irrefl u
            (huv ▸ hadj)
        refine ⟨hne, ?_⟩
        rw [fkRectStripGraph_succ_adj_iff] at hadj
        rcases hadj with hprior | ⟨a, hopen, hedge⟩
        · cases u with
          | inl u =>
              cases v with
              | inl v =>
                  have hp : (fkRectStripGraph hW n priorLayers).Adj u v := by
                    simpa only [SimpleGraph.sum_adj] using hprior
                  obtain ⟨_, i, a, hopen, hcoord⟩ :=
                    (ih priorLayers u v).1 hp
                  refine ⟨i.castSucc, a, hopen, ?_⟩
                  rw [fkRectCoordinateLayerEdge_castSucc]
                  simpa only [Sym2.map_pair_eq,
                    fkRectStripVertexEquiv_inl] using
                    congrArg (Sym2.map rowCast) hcoord
              | inr v => simp only [SimpleGraph.sum_adj] at hprior
          | inr u =>
              cases v with
              | inl v => simp only [SimpleGraph.sum_adj] at hprior
              | inr v => simp only [SimpleGraph.sum_adj,
                  SimpleGraph.bot_adj] at hprior
        · refine ⟨Fin.last n, a, hopen, ?_⟩
          rw [fkRectCoordinateLayerEdge_last]
          have hedge' := (SimpleGraph.adj_edge _ _).1 hedge
          simpa only [Sym2.map_pair_eq] using
            congrArg (Sym2.map (fkRectStripVertexEquiv W (n + 1)))
              hedge'.1
      · rintro ⟨hne, i, a, hopen, hcoord⟩
        rw [fkRectStripGraph_succ_adj_iff]
        revert a
        refine Fin.lastCases ?_ (fun j => ?_) i
        · intro a hopen hcoord
          refine Or.inr ⟨a, hopen, ?_⟩
          apply (SimpleGraph.adj_edge _ _).2
          refine ⟨?_, hne⟩
          rw [fkRectCoordinateLayerEdge_last] at hcoord
          apply (sym2_map_eq_map_iff_of_injective
            (fkRectStripVertexEquiv W (n + 1))
            (fkRectStripVertexEquiv W (n + 1)).injective _ _).1
          simpa only [Sym2.map_pair_eq] using hcoord
        · intro a hopen hcoord
          rw [fkRectCoordinateLayerEdge_castSucc] at hcoord
          cases u with
          | inl u =>
              cases v with
              | inl v =>
                  refine Or.inl ?_
                  change (fkRectStripGraph hW n priorLayers).Adj u v
                  apply (ih priorLayers u v).2
                  refine ⟨fun huv => hne (congrArg Sum.inl huv),
                    j, a, hopen, ?_⟩
                  apply (sym2_map_eq_map_iff_of_injective
                    rowCast hrowCast _ _).1
                  simpa only [Sym2.map_pair_eq,
                    fkRectStripVertexEquiv_inl] using hcoord
              | inr v =>
                  exfalso
                  exact sym2_fkRectStripRowCast_ne_cast_last
                    (fkRectCoordinateLayerEdge hW j
                      (layers j.castSucc).1 a)
                    (fkRectStripVertexEquiv W n u) v (by
                      simpa only [fkRectStripVertexEquiv_inl,
                        fkRectStripVertexEquiv_inr] using hcoord)
          | inr u =>
              cases v with
              | inl v =>
                  exfalso
                  exact sym2_fkRectStripRowCast_ne_cast_last
                    (fkRectCoordinateLayerEdge hW j
                      (layers j.castSucc).1 a)
                    (fkRectStripVertexEquiv W n v) u (by
                      simpa only [fkRectStripVertexEquiv_inl,
                        fkRectStripVertexEquiv_inr, Sym2.eq_swap]
                        using hcoord)
              | inr v =>
                  exfalso
                  exact sym2_fkRectStripRowCast_ne_last_last
                    (fkRectCoordinateLayerEdge hW j
                      (layers j.castSucc).1 a) u v (by
                      simpa only [fkRectStripVertexEquiv_inr] using hcoord)


end
end StatMech.FrontierD
