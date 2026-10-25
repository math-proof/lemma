/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualRectangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualContour.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle
open Finset SimpleGraph Set


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

noncomputable section

noncomputable def ons_touchingBondEquivPlusDualEdge (n : Nat) :
    {edge // edge ∈ bondFinsetTouch 2 n} ≃
      {edge // edge ∈ ons_plusDualFaceEdgeSet n} where
  toFun edge := ⟨flankFacesSym edge.1,
    ons_flankFacesSym_mem_plusDualFaceEdgeSet n edge.2⟩
  invFun edge := ⟨symPrimalSym edge.1,
    ons_symPrimalSym_mem_bondFinsetTouch n edge.2⟩
  left_inv edge := by
    apply Subtype.ext
    obtain ⟨⟨p, q⟩, hpq⟩ := edge.1.exists_rep
    have he : s(p, q) ∈ bondFinsetTouch 2 n := by
      simpa only [← hpq] using edge.2
    have hadj : (hypercubicLattice 2).Adj p q :=
      adj_of_mem_bondFinsetTouch he
    change symPrimalSym (flankFacesSym edge.1) = edge.1
    rw [← hpq, flankFacesSym_mk]
    exact symPrimalSym_flankFaces hadj
  right_inv edge := by
    apply Subtype.ext
    obtain ⟨⟨f, g⟩, hfg⟩ := edge.1.exists_rep
    have hedge : s(f, g) ∈ (hypercubicLattice 2).edgeSet := by
      simpa only [← hfg] using edge.2.1
    have hadj : (hypercubicLattice 2).Adj f g :=
      (SimpleGraph.mem_edgeSet _).mp hedge
    change flankFacesSym (symPrimalSym edge.1) = edge.1
    rw [← hfg, symPrimalSym_mk]
    exact flankFacesSym_symPrimal hadj


noncomputable def ons_plusDualCoordEquiv (n : Nat) :
    {z : Int // -(n : Int) - 1 <= z ∧ z <= n} ≃ Fin ((2 * n + 1) + 1) where
  toFun z := ⟨(z.1 + n + 1).toNat, by
    have hz := z.2
    omega⟩
  invFun k := ⟨(k : Int) - n - 1, by
    have hk := k.2
    constructor <;> omega⟩
  left_inv z := by
    apply Subtype.ext
    simp only
    rw [Int.toNat_of_nonneg (by omega : 0 <= z.1 + n + 1)]
    omega
  right_inv k := by
    apply Fin.ext
    simp only
    have hk := k.2
    rw [show (k : Int) - n - 1 + n + 1 = (k : Int) by ring]
    exact Int.toNat_natCast k


noncomputable def ons_plusDualFaceEquivRect (n : Nat) :
    ons_PlusDualFaceVertex n ≃ ons_RectDualVertex (2 * n + 1) (2 * n + 1) where
  toFun f :=
    (ons_plusDualCoordEquiv n ⟨f.1 0, f.2 0⟩,
      ons_plusDualCoordEquiv n ⟨f.1 1, f.2 1⟩)
  invFun f :=
    ⟨![((ons_plusDualCoordEquiv n).symm f.1).1,
        ((ons_plusDualCoordEquiv n).symm f.2).1], by
      intro i
      fin_cases i
      · exact ((ons_plusDualCoordEquiv n).symm f.1).2
      · exact ((ons_plusDualCoordEquiv n).symm f.2).2⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    fin_cases i
    · exact congrArg Subtype.val
        ((ons_plusDualCoordEquiv n).symm_apply_apply ⟨f.1 0, f.2 0⟩)
    · exact congrArg Subtype.val
        ((ons_plusDualCoordEquiv n).symm_apply_apply ⟨f.1 1, f.2 1⟩)
  right_inv f := by
    apply Prod.ext <;> exact (ons_plusDualCoordEquiv n).apply_symm_apply _

end
end StatMech.Onsager
