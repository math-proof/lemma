module
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
public import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
public import Abbrev.StatisticalMechanics.Code.FrontierB.FiniteCurrentLaw
open MeasureTheory
open scoped ENNReal BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentLaw.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FrontierB

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def currentRawMass (beta : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (m : EdgeCurrent G) : ENNReal :=
  ENNReal.ofReal
    (if sources G (ofEdgeFun G m) = A then weight G beta J (ofEdgeFun G m) else 0)


end FrontierB
end StatMech
