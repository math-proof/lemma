/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Instance.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


def finiteCRSFWitness (V : Type*) [Fintype V] [DecidableEq V] :=
  Σ sigma : Equiv.Perm V, laplacianPermutationFixedPoint sigma -> V

end StatMech.FrontierA
