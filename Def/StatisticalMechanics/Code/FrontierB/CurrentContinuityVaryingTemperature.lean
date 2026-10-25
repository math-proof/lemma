/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityVaryingTemperature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityMagnetizationFK
import Theorem.StatisticalMechanics.Code.Ising.FreeStateDLR
import Mathlib.Topology.UniformSpace.CompactConvergence
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityVaryingTemperature
open Filter MeasureTheory ProbabilityTheory MeasurableSpace Set Topology
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction UniformConvergence


namespace StatMech.FrontierB

open ConfigSpace Ising Lattice

variable {d : Nat}


noncomputable def specApplyBetaContinuousMap
    (n : Nat) (B : Finset (Sym2 (Site d))) (h : Real)
    (f : ConfigSpace (Site d) →ᵇ Real) :
    C(Real × ConfigSpace (Site d), Real) :=
  ⟨fun z => specApply n B z.1 h (f : ConfigSpace (Site d) → Real) z.2,
    continuous_specApply_beta_boundary n B h f⟩


end StatMech.FrontierB
