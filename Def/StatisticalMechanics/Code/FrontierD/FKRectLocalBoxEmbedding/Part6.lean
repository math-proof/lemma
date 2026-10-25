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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding.Part6
open MeasureTheory StatMech.Lattice StatMech.Percolation SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectLocalBoxEmbedding
    (R : FKRectTorus) (center : R.Vertex)
    (m cut lower upper : Nat)
    (hfit : FKRectLocalBoxFits R center m cut lower upper) :
    FK.boxVerts 2 m -> FKRectRightStripBandVertex R cut lower upper :=
  fun z => ⟨fkRectLocalBoxVertex R center z, by
    let p := fkRectSquareUndevelopPoint (fkRectLocalBoxPoint R center z)
    have hp := hfit.2 z
    have hpoint := fkRectVertexSquarePoint_localBoxVertex
      R center m cut lower upper hfit z
    have hundev := congrArg fkRectSquareUndevelopPoint hpoint
    simp only [fkRectVertexSquarePoint,
      fkRectSquareUndevelopPoint_developPoint] at hundev
    have hx : ((fkRectLocalBoxVertex R center z).1.val : Int) = p.1 :=
      congrArg Prod.fst hundev
    have hy : ((fkRectLocalBoxVertex R center z).2.val : Int) = p.2 :=
      congrArg Prod.snd hundev
    change cut <= (fkRectLocalBoxVertex R center z).1.val ∧
      lower <= (fkRectLocalBoxVertex R center z).2.val ∧
      (fkRectLocalBoxVertex R center z).2.val <= upper
    constructor
    · exact_mod_cast (hx.symm ▸ hp.1)
    constructor
    · exact_mod_cast (hy.symm ▸ hp.2.2.1)
    · exact_mod_cast (hy.symm ▸ hp.2.2.2)⟩

end
end StatMech.FrontierD
