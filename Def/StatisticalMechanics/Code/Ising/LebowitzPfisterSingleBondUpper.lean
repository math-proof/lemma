/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBondUpper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterSingleBondUpper
open Set


namespace StatMech.Ising

noncomputable section

def singleBondInterfaceFreeEnergy (K m1 m2 : Real) : Real :=
  Real.log ((1 + m1 * m2 * Real.tanh K) /
    (1 - m1 * m2 * Real.tanh K))


end
end StatMech.Ising
