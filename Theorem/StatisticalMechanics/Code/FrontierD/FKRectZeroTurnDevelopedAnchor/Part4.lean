/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenBoundaryDependence
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part3
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRawPrimalCrossingVerticalPotential_eq_walk
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    {y : R.Vertex}
    (p : (fkRectOpenGraph R omega).Walk
      (fkRectRawPrimalCrossingBase R omega X) y) :
    fkRectRawPrimalCrossingVerticalPotential R omega X y =
      (fkRectWalkWinding R p).2 := by
  classical
  unfold fkRectRawPrimalCrossingVerticalPotential
  rw [dif_pos ⟨p⟩]
  let q : (fkRectOpenGraph R omega).Walk
      (fkRectRawPrimalCrossingBase R omega X) y :=
    Classical.choice ⟨p⟩
  have hclosed := fkRectClosedOpenWalk_verticalWinding_eq_zero_of_remainder
    R omega C (p.append q.reverse)
  rw [fkRectWalkWinding_append, fkRectWalkWinding_reverse] at hclosed
  change (fkRectWalkWinding R p).2 - (fkRectWalkWinding R q).2 = 0 at hclosed
  change (fkRectWalkWinding R q).2 = (fkRectWalkWinding R p).2
  linarith


theorem fkRectRawPrimalCrossingVerticalPotential_sub_eq_walk
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    {x y : R.Vertex}
    (hx : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) x)
    (p : (fkRectOpenGraph R omega).Walk x y) :
    fkRectRawPrimalCrossingVerticalPotential R omega X y -
        fkRectRawPrimalCrossingVerticalPotential R omega X x =
      (fkRectWalkWinding R p).2 := by
  let q : (fkRectOpenGraph R omega).Walk
      (fkRectRawPrimalCrossingBase R omega X) x := Classical.choice hx
  have hy : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) y := ⟨q.append p⟩
  rw [fkRectRawPrimalCrossingVerticalPotential_eq_walk R omega C X q,
    fkRectRawPrimalCrossingVerticalPotential_eq_walk R omega C X
      (q.append p),
    fkRectWalkWinding_append]
  ring


end
end StatMech.FrontierD
