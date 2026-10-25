/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplit.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable def kwLocalAngularInternalExitSolution
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) :
    Matrix (KWOrderedInternalSplitDart G (data.order))
      G.Dart ℂ := fun d e ↦ by
        classical
        exact if KWOrderedInternalDartFacesPort (data.order)
            d (kwPortOfDart G e) then
          data.root (kwPortOfDart G e) else 0

end StatMech.FrontierA
