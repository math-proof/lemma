/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Inductive.StatisticalMechanics.Code.Walls.euceuler
open scoped BigOperators
open Finset


namespace StatMech.Euc

theorem euc_chi_induction {K : Finset Cell} (hK : EucBuildable K) : regChi K = 1 := by
  induction hK with
  | singleton c => exact euc_chi_singleton c
  | attach c K _ hc harc ih => rw [euc_chi_attach c K hc harc]; exact ih


theorem euc_buildable_nonempty {K : Finset Cell} (hK : EucBuildable K) : K.Nonempty := by
  induction hK with
  | singleton c => exact ⟨c, mem_singleton_self c⟩
  | attach c K _ _ _ _ => exact ⟨c, mem_insert_self c K⟩


lemma euc_regChi_eval (K : Finset Cell) :
    regChi K = ((regVerts K).card : ℤ) - (regEdges K).card + K.card := rfl


theorem euc_chi_domino : regChi {((0 : ℤ), (0 : ℤ)), (1, 0)} = 1 := by
  have hv : (regVerts {((0 : ℤ), (0 : ℤ)), (1, 0)}).card = 6 := by decide
  have he : (regEdges {((0 : ℤ), (0 : ℤ)), (1, 0)}).card = 7 := by decide
  rw [euc_regChi_eval, hv, he]
  decide


theorem euc_chi_box2 :
    regChi {((0 : ℤ), (0 : ℤ)), (1, 0), (0, 1), (1, 1)} = 1 := by
  have hv : (regVerts {((0 : ℤ), (0 : ℤ)), (1, 0), (0, 1), (1, 1)}).card = 9 := by decide
  have he : (regEdges {((0 : ℤ), (0 : ℤ)), (1, 0), (0, 1), (1, 1)}).card = 12 := by decide
  rw [euc_regChi_eval, hv, he]
  decide


theorem euc_chi_Ltromino : regChi {((0 : ℤ), (0 : ℤ)), (1, 0), (0, 1)} = 1 := by
  have hv : (regVerts {((0 : ℤ), (0 : ℤ)), (1, 0), (0, 1)}).card = 8 := by decide
  have he : (regEdges {((0 : ℤ), (0 : ℤ)), (1, 0), (0, 1)}).card = 10 := by decide
  rw [euc_regChi_eval, hv, he]
  decide


theorem euc_chi_holeyRing :
    regChi ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)} : Finset Cell) = 0 := by
  have hv : (regVerts ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)}
      : Finset Cell)).card = 16 := by decide
  have he : (regEdges ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)}
      : Finset Cell)).card = 24 := by decide
  rw [euc_regChi_eval, hv, he]
  decide


theorem euc_buildable_domino :
    EucBuildable ({((0:ℤ),(0:ℤ)), (1,0)} : Finset Cell) := by
  have h : (insert ((1:ℤ),(0:ℤ)) {((0:ℤ),(0:ℤ))} : Finset Cell)
      = ({((0:ℤ),(0:ℤ)), (1,0)} : Finset Cell) := by decide
  rw [← h]
  refine EucBuildable.attach ((1:ℤ),(0:ℤ)) {((0:ℤ),(0:ℤ))}
    (EucBuildable.singleton _) (by decide) (by decide)


theorem euc_buildable_Ltromino :
    EucBuildable ({((0:ℤ),(0:ℤ)), (1,0), (0,1)} : Finset Cell) := by
  have h : (insert ((0:ℤ),(1:ℤ)) {((0:ℤ),(0:ℤ)), (1,0)} : Finset Cell)
      = ({((0:ℤ),(0:ℤ)), (1,0), (0,1)} : Finset Cell) := by decide
  rw [← h]
  refine EucBuildable.attach ((0:ℤ),(1:ℤ)) {((0:ℤ),(0:ℤ)), (1,0)}
    euc_buildable_domino (by decide) (by decide)


end StatMech.Euc
