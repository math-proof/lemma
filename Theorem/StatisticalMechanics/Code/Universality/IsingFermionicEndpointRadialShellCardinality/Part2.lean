/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialShellCardinality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicRadialResidualSummation
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerCardinality.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFaceCornerCardinality.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRadialShellCardinality.Part2


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem vertexEndpointRadialShellCode_injective
    (n r : Nat)
    {z w : Option (FKIsingSquareFullVertexNode n)}
    (hz : vertexEndpointRadialShell n z = r)
    (hw : vertexEndpointRadialShell n w = r)
    (hcode : vertexEndpointRadialShellCode n r z hz =
      vertexEndpointRadialShellCode n r w hw) :
    z = w := by
  cases z with
  | none =>
      cases w with
      | none => rfl
      | some y =>
          by_cases hy : fullVertexRowIndex n y <=
              2 * n - fullVertexRowIndex n y <;>
            simp [vertexEndpointRadialShellCode, hy] at hcode
  | some x =>
      cases w with
      | none =>
          by_cases hx : fullVertexRowIndex n x <=
              2 * n - fullVertexRowIndex n x <;>
            simp [vertexEndpointRadialShellCode, hx] at hcode
      | some y =>
          by_cases hx : fullVertexRowIndex n x <=
              2 * n - fullVertexRowIndex n x <;>
            by_cases hy : fullVertexRowIndex n y <=
              2 * n - fullVertexRowIndex n y
          · simp [vertexEndpointRadialShellCode, hx, hy] at hcode
            have hcol : fullVertexColumnIndex n x =
                fullVertexColumnIndex n y := hcode
            have hxrad : fullVertexColumnIndex n x +
                fullVertexRowIndex n x = r := by
              simpa [vertexEndpointRadialShell, min_eq_left hx] using hz
            have hyrad : fullVertexColumnIndex n y +
                fullVertexRowIndex n y = r := by
              simpa [vertexEndpointRadialShell, min_eq_left hy] using hw
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
          · simp [vertexEndpointRadialShellCode, hx, hy] at hcode
          · simp [vertexEndpointRadialShellCode, hx, hy] at hcode
          · simp [vertexEndpointRadialShellCode, hx, hy] at hcode
            have hcol : fullVertexColumnIndex n x =
                fullVertexColumnIndex n y := hcode
            have hxupper : 2 * n - fullVertexRowIndex n x <=
                fullVertexRowIndex n x := by omega
            have hyupper : 2 * n - fullVertexRowIndex n y <=
                fullVertexRowIndex n y := by omega
            have hxrad : fullVertexColumnIndex n x +
                (2 * n - fullVertexRowIndex n x) = r := by
              simpa [vertexEndpointRadialShell, min_eq_right hxupper] using hz
            have hyrad : fullVertexColumnIndex n y +
                (2 * n - fullVertexRowIndex n y) = r := by
              simpa [vertexEndpointRadialShell, min_eq_right hyupper] using hw
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

theorem vertexEndpointRadialShell_card_le (n r : Nat) :
    (Finset.univ.filter (fun z : Option (FKIsingSquareFullVertexNode n) =>
      vertexEndpointRadialShell n z = r)).card <= 3 * (r + 1) := by
  classical
  let S := Finset.univ.filter
    (fun z : Option (FKIsingSquareFullVertexNode n) =>
      vertexEndpointRadialShell n z = r)
  let encode : {z // z ∈ S} -> Fin 3 × Fin (r + 1) := fun z =>
    vertexEndpointRadialShellCode n r z.1 (by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using z.2)
  have hinj : Function.Injective encode := by
    intro z w hzw
    apply Subtype.ext
    exact vertexEndpointRadialShellCode_injective n r _ _ hzw
  have hcard : Fintype.card {z // z ∈ S} <=
      Fintype.card (Fin 3 × Fin (r + 1)) :=
    Fintype.card_le_of_injective encode hinj
  change S.card <= 3 * (r + 1)
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using
    hcard


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
