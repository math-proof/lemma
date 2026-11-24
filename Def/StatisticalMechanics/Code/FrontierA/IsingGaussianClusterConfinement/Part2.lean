module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterDisentangling
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFourCurrent
public import Theorem.StatisticalMechanics.Code.Ising.FreeCorrelationDomainMonotonicity
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterConfinement
open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterConfinement.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteTreeSafeRegionFiber
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (roots T : Finset V)
    (A C : Finset V) : Real :=
  gatedSourcePairSum G beta J A C
    (fun n => finiteTreeSafeRegion G n roots = T)

noncomputable def finiteTreeSafeRegionContext
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (roots T : Finset V) : Real :=
  ∑' bd, claim1Context G beta J T
    (fun n => finiteTreeSafeRegion G n roots = T) ∅ ∅ bd

end StatMech.FrontierA
