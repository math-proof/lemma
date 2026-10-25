/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint.Part3
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopHighTempResummation.Part2
open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Ising StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def ons_reciprocalInterpolationCoeff (q : Complex) (s : Fin 3) : Complex :=
  if s = 0 then q ^ 2 - (q ^ 2)⁻¹
  else if s = 1 then ((q ^ 2)⁻¹ + 1) / 2
  else ((q ^ 2)⁻¹ - 1) / 2


def ons_reciprocalInterpolationValue (q : Complex) (s : Fin 3) : Complex :=
  if s = 0 then 0 else if s = 1 then q else -q

end
end StatMech.Onsager
