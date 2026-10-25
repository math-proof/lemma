/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonPairLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MassTransport
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonPairLaw.Part2
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


noncomputable def interpolatedHighPairLaw (T : MonotoneAutomaton d)
    (mu : Measure (FieldTriple d)) : Measure (PairSiteConfig d) :=
  Measure.map (interpolatedHighPair T) mu


end StatMech.FrontierA
