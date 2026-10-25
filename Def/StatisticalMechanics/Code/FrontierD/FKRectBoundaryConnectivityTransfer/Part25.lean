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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part22
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectStripSuccEquiv (W n : Nat) :
    (Fin W × Fin (n + 1)) ⊕ Fin W ≃ Fin W × Fin (n + 2) where
  toFun
    | Sum.inl z => (z.1, z.2.castSucc)
    | Sum.inr x => (x, Fin.last (n + 1))
  invFun z := Fin.lastCases (Sum.inr z.1)
    (fun y => Sum.inl (z.1, y)) z.2
  left_inv z := by
    cases z with
    | inl z => simp
    | inr x => simp
  right_inv z := by
    rcases z with ⟨x, y⟩
    refine Fin.lastCases ?_ (fun i => ?_) y
    · simp
    · simp


def fkRectStripVertexEquiv (W : Nat) :
    (n : Nat) -> FKRectStripVertex W n ≃ Fin W × Fin (n + 1)
  | 0 =>
      { toFun := fun x => (x, 0)
        invFun := fun z => z.1
        left_inv := by intro x; rfl
        right_inv := by
          rintro ⟨x, y⟩
          apply Prod.ext
          · rfl
          · exact (Fin.eq_zero y).symm }
  | n + 1 =>
      (Equiv.sumCongr (fkRectStripVertexEquiv W n)
        (Equiv.refl (Fin W))).trans (fkRectStripSuccEquiv W n)

end
end StatMech.FrontierD
