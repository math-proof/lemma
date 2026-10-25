/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIndependentDisentangling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterConfinement.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIntersectionUnionBound.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedEq22Refinement
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIndependentDisentangling
open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]


abbrev IndependentPairProfiles
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)

abbrev IndependentFourProfiles
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  IndependentPairProfiles G × IndependentPairProfiles G

end StatMech.FrontierA
