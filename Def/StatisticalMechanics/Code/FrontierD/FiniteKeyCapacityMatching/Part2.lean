/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteKeyCapacityMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteKeyCapacityMatching
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def finiteKeyCapacityCopiesEquiv
    {Source Key : Type*} [Fintype Source] [Fintype Key]
    [DecidableEq Key] (keyOf : Source -> Key) :
    Source ≃ FiniteKeyCapacityCopies Key
      (fun key => Fintype.card {source : Source // keyOf source = key}) :=
  (Equiv.sigmaFiberEquiv keyOf).symm.trans
    (Equiv.sigmaCongrRight fun _ => Fintype.equivFin _)

end
end StatMech.FrontierD
