/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapLambertProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Ring.InfiniteSum
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable def sixVertexGapAlternatingLogSeries (lam : ℝ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n *
    Real.log (1 + Real.exp (-2 * ((n + 1 : ℝ) * lam)))

noncomputable def gapLogDoubleTerm (q : ℝ) (p : ℕ × ℕ) : ℝ :=
  (-1 : ℝ) ^ p.1 * (-1 : ℝ) ^ p.2 *
    q ^ ((p.1 + 1) * (p.2 + 1)) / (p.2 + 1 : ℝ)

end StatMech.FrontierD
