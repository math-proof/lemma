/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCycleComponentExchange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

def exchangeCyclePair (A B : Finset I)
    (p : Finset I × Finset I) : Finset I × Finset I :=
  ((p.1 \ A) ∪ (p.2 ∩ B), (p.2 \ B) ∪ (p.1 ∩ A))

end StatMech.GrahamGHS.FourColor
