/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MeasurableFKGClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FreeDLRExtreme
import Theorem.StatisticalMechanics.Code.Probability.InfiniteHarris.Part3
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Profinite
import Theorem.StatisticalMechanics.Code.Probability.MeasurableFKGClosure.Part2
open Filter MeasureTheory Set Topology


namespace StatMech

variable {E : Type*} [DecidableEq E] [Countable E]

def configUpwardClosure (K : Set (ConfigSpace E)) : Set (ConfigSpace E) :=
  {eta | ∃ omega ∈ K, omega ≤ eta}

end StatMech
