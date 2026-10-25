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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part27
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fin_exists_castSucc_or_last {n : Nat} {P : Fin (n + 1) -> Prop} :
    (∃ i, P i) ↔ (∃ i : Fin n, P i.castSucc) ∨ P (Fin.last n) := by
  constructor
  · rintro ⟨i, hi⟩
    revert hi
    refine Fin.lastCases ?_ (fun j hj => ?_) i
    · exact Or.inr
    · exact Or.inl ⟨j, hj⟩
  · rintro (⟨i, hi⟩ | hi)
    · exact ⟨i.castSucc, hi⟩
    · exact ⟨Fin.last n, hi⟩

theorem fkRectCoordinateLayerEdge_castSucc
    {W n : Nat} (hW : 0 < W) (i : Fin n) (evenRow : Bool)
    (a : Bool × Fin W) :
    fkRectCoordinateLayerEdge hW i.castSucc evenRow a =
      Sym2.map (fun z : Fin W × Fin (n + 1) => (z.1, z.2.castSucc))
        (fkRectCoordinateLayerEdge hW i evenRow a) := by
  rcases a with ⟨dir, x⟩
  cases dir <;> cases evenRow <;>
    rfl

theorem fkRectCoordinateLayerEdge_last
    {W : Nat} (hW : 0 < W) (n : Nat) (evenRow : Bool)
    (a : Bool × Fin W) :
    fkRectCoordinateLayerEdge hW (Fin.last n) evenRow a =
      Sym2.map (fkRectStripVertexEquiv W (n + 1))
        s(fkRectStripLayerEmbed n
            (fkRectLayerEdgeEndpoints hW evenRow a).1,
          fkRectStripLayerEmbed n
            (fkRectLayerEdgeEndpoints hW evenRow a).2) := by
  rw [Sym2.map_pair_eq]
  exact congrArg (fun e => s(e.1, e.2))
    (fkRectCoordinateLayerEdgeEndpoints_last hW n evenRow a).symm

theorem sym2_map_eq_map_iff_of_injective
    {A B : Type*} (f : A -> B) (hf : Function.Injective f)
    (e e' : Sym2 A) : Sym2.map f e = Sym2.map f e' ↔ e = e' := by
  constructor
  · intro h
    induction e using Sym2.inductionOn with
    | _ a b =>
      induction e' using Sym2.inductionOn with
      | _ c d =>
        simp only [Sym2.map_pair_eq, Sym2.eq_iff] at h ⊢
        rcases h with h | h
        · exact Or.inl ⟨hf h.1, hf h.2⟩
        · exact Or.inr ⟨hf h.1, hf h.2⟩
  · exact congrArg (Sym2.map f)

end
end StatMech.FrontierD
