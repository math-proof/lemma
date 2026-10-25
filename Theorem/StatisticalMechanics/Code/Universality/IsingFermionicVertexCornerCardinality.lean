/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerCardinality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerGreen.Part5
import Def.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerCardinality


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem vertexMarkedEndpointCode_injective
    (n radius : Nat)
    {z w : Option (FKIsingSquareFullVertexNode n)}
    (hz : vertexMarkedEndpointLayer n radius z)
    (hw : vertexMarkedEndpointLayer n radius w)
    (hcode : vertexMarkedEndpointCode n radius z hz =
      vertexMarkedEndpointCode n radius w hw) :
    z = w := by
  cases z with
  | none => exact False.elim hz
  | some x =>
      cases w with
      | none => exact False.elim hw
      | some y =>
          by_cases hx : fullVertexColumnIndex n x +
              fullVertexRowIndex n x <= radius <;>
            by_cases hy : fullVertexColumnIndex n y +
              fullVertexRowIndex n y <= radius
          · simp [vertexMarkedEndpointCode, hx, hy] at hcode
            have hcol : fullVertexColumnIndex n x =
                fullVertexColumnIndex n y := hcode.1
            have hrow : fullVertexRowIndex n x =
                fullVertexRowIndex n y := hcode.2
            apply congrArg some
            apply Subtype.ext
            funext i
            fin_cases i
            · have hxc := fullVertexColumnIndex_coe n x
              have hyc := fullVertexColumnIndex_coe n y
              change x.1 0 = y.1 0
              omega
            · have hxr := fullVertexRowIndex_coe n x
              have hyr := fullVertexRowIndex_coe n y
              change x.1 1 = y.1 1
              omega
          · simp [vertexMarkedEndpointCode, hx, hy] at hcode
          · simp [vertexMarkedEndpointCode, hx, hy] at hcode
          · simp [vertexMarkedEndpointCode, hx, hy] at hcode
            have hcol : fullVertexColumnIndex n x =
                fullVertexColumnIndex n y := hcode.1
            have htopdist : 2 * n - fullVertexRowIndex n x =
                2 * n - fullVertexRowIndex n y := hcode.2
            apply congrArg some
            apply Subtype.ext
            funext i
            fin_cases i
            · have hxc := fullVertexColumnIndex_coe n x
              have hyc := fullVertexColumnIndex_coe n y
              change x.1 0 = y.1 0
              omega
            · have hxr := fullVertexRowIndex_coe n x
              have hyr := fullVertexRowIndex_coe n y
              have hxb := fullVertexRowIndex_le n x
              have hyb := fullVertexRowIndex_le n y
              change x.1 1 = y.1 1
              omega


theorem vertexInteriorExceptionalSources_card_le
    (n radius : Nat) :
    (isingFiniteWeightedInteriorExceptionalSources
      (vertexDirichletBoundary n)
      (vertexMarkedEndpointLayer n radius)).card <=
        2 * (radius + 1) ^ 2 := by
  classical
  let S := isingFiniteWeightedInteriorExceptionalSources
    (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)
  let encode : {z // z ∈ S} ->
      Bool × Fin (radius + 1) × Fin (radius + 1) := fun z =>
    vertexMarkedEndpointCode n radius z.1 (by
      have hzmem : z.1 ∈ isingFiniteWeightedInteriorExceptionalSources
          (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius) := by
        simpa only [S] using z.2
      change z.1 ∈ Finset.univ.filter (fun w =>
        Not (vertexDirichletBoundary n w) ∧
          vertexMarkedEndpointLayer n radius w) at hzmem
      exact (Finset.mem_filter.mp hzmem).2.2)
  have hinj : Function.Injective encode := by
    intro z w hzw
    apply Subtype.ext
    exact vertexMarkedEndpointCode_injective n radius _ _ hzw
  have hcard : Fintype.card {z // z ∈ S} <=
      Fintype.card (Bool × Fin (radius + 1) × Fin (radius + 1)) :=
    Fintype.card_le_of_injective encode hinj
  simpa [S, pow_two, mul_assoc] using hcard

theorem vertexInteriorExceptionalSources_mul_le
    (n radius : Nat) (B : Real) (hB : 0 <= B) :
    ((isingFiniteWeightedInteriorExceptionalSources
      (vertexDirichletBoundary n)
      (vertexMarkedEndpointLayer n radius)).card : Real) * B <=
        (2 * (radius + 1) ^ 2 : Nat) * B := by
  apply mul_le_mul_of_nonneg_right _ hB
  exact_mod_cast vertexInteriorExceptionalSources_card_le n radius


theorem vertexMarkedEndpointBarrier_le_radiusDistance
    (n radius : Nat) (distance : Real)
    (source : FKIsingSquareFullVertexNode n)
    (hn : 0 < n)
    (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
    (hright : source.1 0 < (n : Int))
    (hbottom : -(n : Int) < source.1 1)
    (htop : source.1 1 < (n : Int))
    (hdistance : 0 < distance)
    (hlowerDistance : distance <=
      (fullVertexColumnIndex n source : Real) +
        (fullVertexRowIndex n source : Real) +
          1 / isingFermionicGhostCoefficient)
    (hupperDistance : distance <=
      (fullVertexColumnIndex n source : Real) +
        (2 * n - fullVertexRowIndex n source : Nat) +
          1 / isingFermionicGhostCoefficient) :
    vertexMarkedEndpointBarrier n radius (some source) <=
      (2 * (radius + 1) ^ 2 : Nat) *
        ((radius : Real) *
          ((radius : Real) + 1 / isingFermionicGhostCoefficient) /
            distance) := by
  let B : Real :=
    (radius : Real) *
      ((radius : Real) + 1 / isingFermionicGhostCoefficient) / distance
  have hB : 0 <= B := by
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg (Nat.cast_nonneg _)
          (one_div_nonneg.mpr isingFermionicGhostCoefficient_pos.le)))
      hdistance.le
  have hbarrier := vertexMarkedEndpointBarrier_le_card_mul_reciprocal
    n radius (some source) hfixed B
    (vertexPointPoissonBarrier_le_exceptionalSourceRadius
      n radius distance source hn hfixed hright hbottom htop hdistance
      hlowerDistance hupperDistance)
  exact hbarrier.trans
    (vertexInteriorExceptionalSources_mul_le n radius B hB)


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
