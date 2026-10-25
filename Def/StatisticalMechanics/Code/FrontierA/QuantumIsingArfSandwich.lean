/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingArfSandwich.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.SpecialFunctions.Log.Basic


namespace StatMech.FrontierA

noncomputable def arfSectorNormMax (sector : Fin 2 -> Fin 2 -> Complex) : Real :=
  max (max ‖sector 1 1‖ ‖sector 0 1‖)
    (max ‖sector 1 0‖ ‖sector 0 0‖)

end StatMech.FrontierA
