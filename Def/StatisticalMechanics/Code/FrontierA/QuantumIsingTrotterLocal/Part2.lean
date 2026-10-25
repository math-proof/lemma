/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterLocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterLocal


namespace StatMech.FrontierA

noncomputable def quantumIsingTrotterKernel
    (beta h : ℝ) (n : ℕ) (s t : Bool) : ℝ :=
  if s = t then 1 else beta * h / (2 * n)


noncomputable def quantumIsingVerticalCoupling
    (beta h : ℝ) (n : ℕ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (beta * h / (2 * n))


end StatMech.FrontierA
