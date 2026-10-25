/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreFreeDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
open scoped BigOperators
open SimpleGraph


namespace StatMech.FK

noncomputable section

theorem bcProb_congr_boundary {V : Type*} [Fintype V] [DecidableEq V]
    (G C D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel C.Adj] [DecidableRel D.Adj]
    (h : C = D) (p q : Real) (omega : ConfigSpace (Sym2 V)) :
    bcProb G C p q omega = bcProb G D p q omega := by
  subst D
  congr 1

end
end StatMech.FK
