/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KKLWire.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.KestenThresholdRoute
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Theorem.StatisticalMechanics.Code.TwoDim.KKLWire
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace TwoDim

open ConfigSpace Function Finset StatMech StatMech.Sharpness StatMech.BeffaraDC
  StatMech.Probability StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def kklw_logMaxInfl [Nonempty E] (p : ℝ) (A : Set (ConfigSpace E)) : ℝ :=
  Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1:ℝ))))


end TwoDim
end StatMech
