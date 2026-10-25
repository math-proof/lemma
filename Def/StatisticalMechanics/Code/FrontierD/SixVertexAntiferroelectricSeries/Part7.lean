/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy.Part4
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part6
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable def sixVertexAlternatingHarmonicLimit : ℝ :=
  Classical.choose (antitone_one_div_nat_succ.tendsto_alternating_series_of_tendsto_zero
    (by simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))))

end StatMech.FrontierD
