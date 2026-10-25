/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConnectionSymmetry
import Def.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding.Part5
open MeasureTheory StatMech.Lattice StatMech.Percolation SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectLocalBoxFits_of_margin
    (R : FKRectTorus) (center : R.Vertex)
    (m cut lower upper : Nat)
    (hupper : upper < R.height)
    (hcolLower : cut + 2 * m <= center.1.val)
    (hcolUpper : center.1.val + 2 * m < R.width)
    (hrowLower : lower + 2 * m <= center.2.val)
    (hrowUpper : center.2.val + 2 * m <= upper) :
    FKRectLocalBoxFits R center m cut lower upper := by
  refine ⟨hupper, ?_⟩
  intro z
  have hz := z.2
  rw [mem_box] at hz
  have hz0 := hz 0
  have hz1 := hz 1
  dsimp [fkRectLocalBoxPoint, fkRectVertexSquarePoint,
    fkRectSquareDevelopPoint, fkRectSquareUndevelopPoint]
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

@[simp] theorem fkRectSquareSiteOfPair_localBoxPoint
    (R : FKRectTorus) (center : R.Vertex) (z : Site 2) :
    fkRectSquareSiteOfPair (fkRectLocalBoxPoint R center z) =
      fkRectVertexSquareSite R center + z := by
  funext i
  fin_cases i <;>
    simp [fkRectSquareSiteOfPair, fkRectLocalBoxPoint,
      fkRectVertexSquareSite]


theorem fkRectVertexSquarePoint_localBoxVertex
    (R : FKRectTorus) (center : R.Vertex)
    (m cut lower upper : Nat)
    (hfit : FKRectLocalBoxFits R center m cut lower upper)
    (z : FK.boxVerts 2 m) :
    fkRectVertexSquarePoint R (fkRectLocalBoxVertex R center z) =
      fkRectLocalBoxPoint R center z := by
  let t := fkRectLocalBoxPoint R center z
  let p := fkRectSquareUndevelopPoint t
  have hp := hfit.2 z
  have hp0 : (0 : Int) <= p.1 :=
    (Int.natCast_nonneg cut).trans hp.1
  have hp2 : (0 : Int) <= p.2 :=
    (Int.natCast_nonneg lower).trans hp.2.2.1
  have hp2lt : p.2 < (R.height : Int) := by
    exact hp.2.2.2.trans_lt (by exact_mod_cast hfit.1)
  change fkRectSquareDevelopPoint
      (((fkRectSquareRepresentativeVertex R t).1.val : Int),
        ((fkRectSquareRepresentativeVertex R t).2.val : Int)) = t
  have hx : ((fkRectSquareRepresentativeVertex R t).1.val : Int) = p.1 := by
    change ((p.1.natMod R.width : Nat) : Int) = p.1
    rw [Int.natMod, Int.emod_eq_of_lt hp0 hp.2.1]
    exact Int.natCast_toNat_eq_self.mpr hp0
  have hy : ((fkRectSquareRepresentativeVertex R t).2.val : Int) = p.2 := by
    change ((p.2.natMod R.height : Nat) : Int) = p.2
    rw [Int.natMod, Int.emod_eq_of_lt hp2 hp2lt]
    exact Int.natCast_toNat_eq_self.mpr hp2
  rw [hx, hy]
  exact fkRectSquareDevelopPoint_undevelopPoint t


end
end StatMech.FrontierD
