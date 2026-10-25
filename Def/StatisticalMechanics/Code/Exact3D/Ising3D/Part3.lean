/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Ising3D.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.CorrelationLength.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part2
open MeasureTheory


namespace StatMech

namespace Exact3D

open StatMech.Lattice


noncomputable def plusInverseDecayRateOnXAxis (β : ℝ) (n : ℕ) : ℝ :=
  finiteDistanceDecayRate (twoPointOnXAxis β) n


noncomputable def freeInverseDecayRateOnXAxis (β : ℝ) (n : ℕ) : ℝ :=
  finiteDistanceDecayRate (freeTwoPointOnXAxis β) n


noncomputable def plusLowerInverseCorrelationLengthOnXAxis (β : ℝ) : ℝ :=
  Filter.liminf (plusInverseDecayRateOnXAxis β) Filter.atTop


noncomputable def plusUpperInverseCorrelationLengthOnXAxis (β : ℝ) : ℝ :=
  Filter.limsup (plusInverseDecayRateOnXAxis β) Filter.atTop


noncomputable def freeLowerInverseCorrelationLengthOnXAxis (β : ℝ) : ℝ :=
  Filter.liminf (freeInverseDecayRateOnXAxis β) Filter.atTop


noncomputable def freeUpperInverseCorrelationLengthOnXAxis (β : ℝ) : ℝ :=
  Filter.limsup (freeInverseDecayRateOnXAxis β) Filter.atTop


noncomputable def plusLiminfCorrelationLengthOnXAxis (β : ℝ) : ℝ :=
  (plusLowerInverseCorrelationLengthOnXAxis β)⁻¹


noncomputable def freeLiminfCorrelationLengthOnXAxis (β : ℝ) : ℝ :=
  (freeLowerInverseCorrelationLengthOnXAxis β)⁻¹


noncomputable def Ising3DModel : CriticalModel Ising3DSite where
  betaC := Ising.betaC 3
  twoPoint := ising3DPlusTwoPoint


end Exact3D
end StatMech
