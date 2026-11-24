module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy.Part4
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part6
open Finset Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

theorem antitone_one_div_nat_succ :
    Antitone (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) := by
  intro a b hab
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right hab 1

end StatMech.FrontierD
