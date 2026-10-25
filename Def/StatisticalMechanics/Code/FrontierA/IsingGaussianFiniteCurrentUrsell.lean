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
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def finiteCurrentFourthUrsell
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  let Z := currentSum G beta J ∅
  (currentSum G beta J {i, j, k, l} * Z -
    currentSum G beta J {i, j} * currentSum G beta J {k, l} -
    currentSum G beta J {i, k} * currentSum G beta J {j, l} -
    currentSum G beta J {i, l} * currentSum G beta J {j, k}) / Z ^ 2


noncomputable def finiteIsingFourthUrsell
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l : V) : Real :=
  expectationJ G beta J {i, j, k, l} -
    expectationJ G beta J {i, j} * expectationJ G beta J {k, l} -
    expectationJ G beta J {i, k} * expectationJ G beta J {j, l} -
    expectationJ G beta J {i, l} * expectationJ G beta J {j, k}


end StatMech.FrontierA
