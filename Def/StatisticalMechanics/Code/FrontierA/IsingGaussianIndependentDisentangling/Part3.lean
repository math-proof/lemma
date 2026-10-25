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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIndependentDisentangling.Part2
open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteTreeIndependentTotalSummand
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V)
    (z : IndependentFourProfiles G) : Real :=
  ((if sources G (ofEdgeFun G z.1.1) = {i, j}
      then weight G beta J (ofEdgeFun G z.1.1) else 0) *
    (if sources G (ofEdgeFun G z.1.2) = ∅
      then weight G beta J (ofEdgeFun G z.1.2) else 0)) *
  ((if sources G (ofEdgeFun G z.2.1) = {k, l}
      then weight G beta J (ofEdgeFun G z.2.1) else 0) *
    (if sources G (ofEdgeFun G z.2.2) = ∅
      then weight G beta J (ofEdgeFun G z.2.2) else 0))

end StatMech.FrontierA
