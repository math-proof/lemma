/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusMedial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial


namespace StatMech.FrontierD

def fkRectTorusMedialEdgeEquiv (R : FKRectTorus) :
    R.medialTorus.Vertex ≃ R.EdgeIndex :=
  (Equiv.prodCongr
      (((finCongr (Nat.mul_comm 2 R.width)).trans
        (finProdFinEquiv.symm : Fin (R.width * 2) ≃ Fin R.width × Fin 2)).trans
          (Equiv.prodComm (Fin R.width) (Fin 2)))
      (Equiv.refl (Fin R.height))).trans
    ((Equiv.prodAssoc (Fin 2) (Fin R.width) (Fin R.height)).trans
      (Equiv.prodCongr finTwoEquiv (Equiv.refl R.Vertex)))


end StatMech.FrontierD
