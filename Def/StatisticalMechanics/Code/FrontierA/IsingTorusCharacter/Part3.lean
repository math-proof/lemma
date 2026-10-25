/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredReduction
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part2
open Finset
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


noncomputable def isingTorusAveragedTwoPoint
    (beta : Real) (z : IsingDyadicTorus d k) : Real :=
  (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
      Real.exp (-(beta / 2) *
        isingTorusDirichlet (isingTorusSpinField sigma)) *
      ∑ x : IsingDyadicTorus d k,
        isingTorusSpinField sigma x *
          isingTorusSpinField sigma (x + z)) /
    (isingTorusShiftedPartition (d := d) (k := k) beta 0 *
      Fintype.card (IsingDyadicTorus d k))

end StatMech.FrontierA
