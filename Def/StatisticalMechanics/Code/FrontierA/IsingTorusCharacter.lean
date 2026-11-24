module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredReduction
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
open Finset
open scoped BigOperators ComplexConjugate


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacter.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


noncomputable def isingTorusCharacterDispersion
    (chi : AddChar (IsingDyadicTorus d k) Complex) : Real :=
  ∑ i : Fin d, Complex.normSq (1 - chi (isingTorusStep i))

end StatMech.FrontierA
