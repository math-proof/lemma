/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFiniteCurrentUrsell.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFourCurrent
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedSurvivorSwitching
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part3
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFiniteCurrentUrsell
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteCurrentTreeDiagram
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  ∑ y : V,
    expectationJ G beta J (grahamPairSupport i y) *
      expectationJ G beta J (grahamPairSupport j y) *
      expectationJ G beta J (grahamPairSupport k y) *
      expectationJ G beta J (grahamPairSupport l y)


noncomputable def finiteCurrentTreeDiagramMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  ∑ y : V,
    currentSum G beta J (grahamPairSupport i y) *
      currentSum G beta J (grahamPairSupport j y) *
      currentSum G beta J (grahamPairSupport k y) *
      currentSum G beta J (grahamPairSupport l y)


end StatMech.FrontierA
