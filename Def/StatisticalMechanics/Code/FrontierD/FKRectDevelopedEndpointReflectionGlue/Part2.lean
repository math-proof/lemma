/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedEndpointReflectionGlue.Part2
open Set


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

def fkRectDevelopedThreeByOneTorusCarrier
    (R : FKRectTorus) (n : Nat) : Set R.Vertex :=
  Set.range fun z : fkRectDevelopedThreeByOneRect n =>
    fkRectDevelopedSquareVertex R n z.1

def fkRectDevelopedThreeByOneCarrierVertex
    (R : FKRectTorus) (n : Nat)
    (z : fkRectDevelopedThreeByOneRect n) :
    fkRectDevelopedThreeByOneTorusCarrier R n :=
  ⟨fkRectDevelopedSquareVertex R n z.1, ⟨z, rfl⟩⟩


def fkRectDevelopedThreeByOneCarrierConnectionEvent
    (R : FKRectTorus) (n : Nat)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n)) : Set R.Configuration :=
  {omega | FKRectConnectedWithin R omega
    (fkRectDevelopedThreeByOneTorusCarrier R n)
    (fkRectDevelopedThreeByOneCarrierVertex R n p.1)
    (fkRectDevelopedThreeByOneCarrierVertex R n p.2)}

noncomputable def fkRectDevelopedThreeByOneCarrierOpenHom
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (omega : R.Configuration) :
    (openSubgraph 2 (fkRectDevelopedSquarePullback R n omega)).induce
        (fkRectDevelopedThreeByOneRect n) →g
      (fkRectOpenGraph R omega).induce
        (fkRectDevelopedThreeByOneTorusCarrier R n) where
  toFun := fkRectDevelopedThreeByOneCarrierVertex R n
  map_rel' := by
    intro z w hzw
    exact (fkRectDevelopedThreeByOneOpenHom
      R n hwidth hheight omega).map_rel hzw

end
end StatMech.FrontierD
