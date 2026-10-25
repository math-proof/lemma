/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterConfinement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterDisentangling
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFourCurrent
import Theorem.StatisticalMechanics.Code.Ising.FreeCorrelationDomainMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterConfinement.Part2
open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteTreeClusterConfinementMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (k l : V) (S : Finset V) : Real :=
  gatedSourcePairSum G beta J {k, l} ∅
    (fun n => k ∈ finiteTreeSafeRegion G n Sᶜ)

end StatMech.FrontierA
