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
open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteTreeIndependentDisjointComponentMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  ∑ S ∈ grahamFirstAdmissibleComponentComplements i j k l k,
    grahamFirstComponentFiber G beta J S i {i, j} ∅ *
      finiteTreeClusterConfinementMass G beta J k l S


end StatMech.FrontierA
