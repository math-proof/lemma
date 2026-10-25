/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Theorem.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentParity.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part2
open MeasureTheory Filter Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierB

open StatMech.Ising StatMech.Lattice StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def spinProdBCF (d : ℕ) (A : Finset (Site d)) :
    BoundedContinuousFunction (ConfigSpace (Site d)) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨spinProd A, continuous_spinProd A⟩

end StatMech.FrontierB
