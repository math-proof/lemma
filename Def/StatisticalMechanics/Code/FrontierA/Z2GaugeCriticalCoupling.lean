/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCriticalCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDualCoupling
import Mathlib.Analysis.SpecialFunctions.Artanh
open Set


namespace StatMech.FrontierA

noncomputable def gaugeCriticalCoupling (betaIsing : Real) : Real :=
  Real.artanh (Real.exp (-2 * betaIsing))

end StatMech.FrontierA
