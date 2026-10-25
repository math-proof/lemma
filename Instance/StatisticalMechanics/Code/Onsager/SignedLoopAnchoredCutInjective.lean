/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopAnchoredCutInjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCut
import Def.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCutInjective
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

variable {V P : Type*} [Fintype V] [DecidableEq V]
  [Fintype P] [DecidableEq P]


noncomputable instance ons_multibondSupportGraph_decidableAdj
    (ends : P → V × V) : DecidableRel (ons_multibondSupportGraph ends).Adj :=
  Classical.decRel _


end
end StatMech.Onsager
