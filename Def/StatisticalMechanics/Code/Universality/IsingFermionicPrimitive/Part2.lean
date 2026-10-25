/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareSwitching
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitive
open Complex


namespace StatMech.Universality

noncomputable section

def isingPrimitiveIncrement (F : Complex) : Real := Complex.normSq F


end
end StatMech.Universality
