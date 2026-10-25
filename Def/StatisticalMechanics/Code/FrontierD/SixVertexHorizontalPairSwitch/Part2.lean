/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalColumnClassification
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalPairSwitch
open Finset


namespace StatMech.FrontierD

noncomputable section

def boolPairAgreementCount (a b c d : Bool) : Nat :=
  (if a = c then 1 else 0) + (if b = d then 1 else 0)

def boolPairCrossAgreementCount (a b c d : Bool) : Nat :=
  (if a = d then 1 else 0) + (if b = c then 1 else 0)

end
end StatMech.FrontierD
