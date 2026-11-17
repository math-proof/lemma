/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/HadamardQuadraticFactorOrder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

open Finset


namespace StatMech.FrontierA

noncomputable section

def hadamardQuadraticFactor (r : Real) (z : ℂ) : ℂ :=
  1 + (r : ℂ) * z ^ 2

end
end StatMech.FrontierA
