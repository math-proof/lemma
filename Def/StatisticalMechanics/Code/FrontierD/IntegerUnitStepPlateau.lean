/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegerUnitStepPlateau.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace StatMech.FrontierD

def IntUnitSteps (f : Nat → Int) : Prop :=
  ∀ n, f (n + 1) ≤ f n + 1 ∧ f n ≤ f (n + 1) + 1


end StatMech.FrontierD
