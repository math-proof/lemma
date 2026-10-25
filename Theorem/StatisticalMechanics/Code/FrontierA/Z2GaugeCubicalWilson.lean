/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalWilson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalWilson
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

theorem cubical_hasEvenPlaquetteStarIncidence {a b c : Nat} :
    HasEvenPlaquetteStarIncidence
      (cubicalPlaquetteIncidence (a := a) (b := b) (c := c))
      cubicalVertexStar := by
  rintro ⟨x, y, z⟩ p
  simp only [cubicalVertexStar, Finset.inter_filter, Finset.inter_univ,
    Finset.card_filter]
  cases p with
  | xy i j k =>
      have hi : i.castSucc ≠ i.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      have hj : j.castSucc ≠ j.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      by_cases h00 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i.castSucc, j.castSucc, k⟩
      · rw [h00]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h10 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i.succ, j.castSucc, k⟩
      · rw [h10]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h01 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i.castSucc, j.succ, k⟩
      · rw [h01]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h11 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i.succ, j.succ, k⟩
      · rw [h11]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      simp [cubicalPlaquetteIncidence, cubicalEdgeEndpoints, hi, hj]
      all_goals split_ifs <;> norm_num <;> aesop
  | xz i j k =>
      have hi : i.castSucc ≠ i.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      have hk : k.castSucc ≠ k.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      by_cases h00 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i.castSucc, j, k.castSucc⟩
      · rw [h00]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h10 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i.succ, j, k.castSucc⟩
      · rw [h10]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h01 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i.castSucc, j, k.succ⟩
      · rw [h01]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h11 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i.succ, j, k.succ⟩
      · rw [h11]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      simp [cubicalPlaquetteIncidence, cubicalEdgeEndpoints, hi, hk]
      all_goals split_ifs <;> norm_num <;> aesop
  | yz i j k =>
      have hj : j.castSucc ≠ j.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      have hk : k.castSucc ≠ k.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      by_cases h00 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i, j.castSucc, k.castSucc⟩
      · rw [h00]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h10 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i, j.succ, k.castSucc⟩
      · rw [h10]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h01 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i, j.castSucc, k.succ⟩
      · rw [h01]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      by_cases h11 : (⟨x, y, z⟩ : CubicalVertex a b c) =
        ⟨i, j.succ, k.succ⟩
      · rw [h11]
        simp_all [cubicalPlaquetteIncidence,
          cubicalEdgeEndpoints]
      simp [cubicalPlaquetteIncidence, cubicalEdgeEndpoints, hj, hk]
      all_goals split_ifs <;> norm_num <;> aesop


theorem cubicalGaugeAction_localGaugeTransform_eq {a b c : Nat}
    (K : CubicalPlaquette a b c → Real)
    (v : CubicalVertex a b c)
    (omega : GaugeConfig (CubicalEdge a b c)) :
    gaugeAction cubicalPlaquetteIncidence K
        (localGaugeTransform cubicalVertexStar v omega) =
      gaugeAction cubicalPlaquetteIncidence K omega :=
  gaugeAction_localGaugeTransform_eq cubicalPlaquetteIncidence
    cubicalVertexStar cubical_hasEvenPlaquetteStarIncidence K v omega


end
end StatMech.FrontierA
