/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTreeDiagramAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianTrivialityReduction.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

variable {X : Type*} [Fintype X] [AddCommGroup X]


def finiteSusceptibility (G : X -> Real) : Real :=
  ∑ x, G x


def finiteIntegratedTreeDiagram (G : X -> Real) : Real :=
  ∑ x₂ : X, ∑ x₃ : X, ∑ x₄ : X, ∑ y : X,
    G y * G (y - x₂) * G (y - x₃) * G (y - x₄)


def finiteIntegratedFourthCumulant (U : X -> X -> X -> Real) : Real :=
  ∑ x₂ : X, ∑ x₃ : X, ∑ x₄ : X, U x₂ x₃ x₄

end StatMech.FrontierA
