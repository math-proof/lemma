/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianSetClusterReplacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterDisentangling
import Theorem.StatisticalMechanics.Code.Ising.FreeCorrelationDomainMonotonicity
open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteTreeCurrentCluster
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : Current V) (A : Finset V) : Finset V :=
  Finset.univ.filter (fun v =>
    exists a, a ∈ A ∧ CurrentConnected G n a v)

end StatMech.FrontierA
