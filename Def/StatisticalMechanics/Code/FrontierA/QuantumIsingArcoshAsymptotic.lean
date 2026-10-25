/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingArcoshAsymptotic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSymbolAsymptotic.Part2
import Mathlib.Analysis.SpecialFunctions.Arcosh
open Filter Set Topology
open scoped Topology


namespace StatMech.FrontierA

noncomputable def arcoshQuadraticRatio (u : Real) : Real :=
  if u = 0 then 2 else u ^ 2 / (Real.cosh u - 1)

end StatMech.FrontierA
