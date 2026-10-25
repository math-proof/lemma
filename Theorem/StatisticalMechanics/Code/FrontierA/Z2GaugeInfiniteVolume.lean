/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing.Part4
open Filter Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem cubicalWilsonExpectation_le_chart
    {a b c A B C : Nat} (ox oy oz : Nat)
    (hx : ox + a ≤ A) (hy : oy + b ≤ B) (hz : oz + c ≤ C)
    {beta : Real} (hbeta : 0 ≤ beta) (L : Finset (CubicalEdge a b c)) :
    gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette a b c => beta) L ≤
      gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette A B C => beta)
        (L.map (cubicalEdgeChart ox oy oz hx hy hz)) := by
  let eEmb := cubicalEdgeChart ox oy oz hx hy hz
  let pEmb := cubicalPlaquetteChart ox oy oz hx hy hz
  let Ksmall := fun _ : CubicalPlaquette a b c => beta
  have hzero : ∀ p, 0 ≤ extendGaugeCoupling pEmb Ksmall p := by
    intro p
    unfold extendGaugeCoupling
    cases (embeddingSplitEquiv pEmb).symm p with
    | inl q => exact hbeta
    | inr q => exact le_rfl
  have hle : ∀ p, extendGaugeCoupling pEmb Ksmall p ≤ beta := by
    intro p
    unfold extendGaugeCoupling
    cases (embeddingSplitEquiv pEmb).symm p with
    | inl q => exact le_rfl
    | inr q => exact hbeta
  calc
    gaugeWilsonExpectation cubicalPlaquetteIncidence Ksmall L =
        gaugeWilsonExpectation cubicalPlaquetteIncidence
          (extendGaugeCoupling pEmb Ksmall) (L.map eEmb) :=
      (gaugeWilsonExpectation_extendGaugeCoupling
        cubicalPlaquetteIncidence cubicalPlaquetteIncidence eEmb pEmb
        (cubicalPlaquetteIncidence_chart ox oy oz hx hy hz) Ksmall L).symm
    _ ≤ gaugeWilsonExpectation cubicalPlaquetteIncidence
          (fun _ : CubicalPlaquette A B C => beta) (L.map eEmb) :=
      gaugeWilsonExpectation_mono_coupling cubicalPlaquetteIncidence
        (extendGaugeCoupling pEmb Ksmall) (fun _ => beta) hzero hle _


theorem cubicalEdgeChart_comp_apply
    {a b c A B C X Y Z : Nat}
    (ox oy oz Ox Oy Oz : Nat)
    (hx : ox + a ≤ A) (hy : oy + b ≤ B) (hz : oz + c ≤ C)
    (hX : Ox + A ≤ X) (hY : Oy + B ≤ Y) (hZ : Oz + C ≤ Z)
    (e : CubicalEdge a b c) :
    cubicalEdgeChart Ox Oy Oz hX hY hZ
        (cubicalEdgeChart ox oy oz hx hy hz e) =
      cubicalEdgeChart (Ox + ox) (Oy + oy) (Oz + oz)
        (by omega) (by omega) (by omega) e := by
  cases e with
  | x i j k =>
      change CubicalEdge.x _ _ _ = CubicalEdge.x _ _ _
      rw [CubicalEdge.x.injEq]
      constructor
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega
      constructor
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega
  | y i j k =>
      change CubicalEdge.y _ _ _ = CubicalEdge.y _ _ _
      rw [CubicalEdge.y.injEq]
      constructor
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega
      constructor
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega
  | z i j k =>
      change CubicalEdge.z _ _ _ = CubicalEdge.z _ _ _
      rw [CubicalEdge.z.injEq]
      constructor
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega
      constructor
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega
      · apply Fin.ext
        simp [finOffsetEmbedding]
        omega


end
end StatMech.FrontierA
