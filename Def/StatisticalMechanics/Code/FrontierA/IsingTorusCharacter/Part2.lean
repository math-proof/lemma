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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter
open Finset
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


noncomputable def isingTorusDirichletBilinearComplex
    (u : IsingDyadicTorus d k → Real)
    (v : IsingDyadicTorus d k → Complex) : Complex :=
  ∑ x : IsingDyadicTorus d k, ∑ i : Fin d,
    (u x - u (x + isingTorusStep i)) *
      (v x - v (x + isingTorusStep i))

end StatMech.FrontierA
