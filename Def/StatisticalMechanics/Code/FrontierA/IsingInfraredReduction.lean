/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Topology.Algebra.Order.LiminfLimsup
open Finset Filter Set Topology
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

variable {Gamma : Type*} [Fintype Gamma] [AddCommGroup Gamma]


noncomputable def finiteTorusFourierCoeff
    (G : Gamma → ℝ) (chi : AddChar Gamma ℂ) : ℂ :=
  ∑ z : Gamma, (G z : ℂ) * chi z


noncomputable def finiteTorusQuadratic
    (G : Gamma → ℝ) (f : Gamma → ℂ) : ℂ :=
  ∑ x : Gamma, ∑ z : Gamma,
    conj (f x) * (G z : ℂ) * f (x + z)


def IsPositiveSemidefiniteTorusKernel (G : Gamma → ℝ) : Prop :=
  ∀ f : Gamma → ℂ, 0 ≤ (finiteTorusQuadratic G f).re


def HasFiniteTorusGaussianDomination
    (G : Gamma → ℝ) (inverseEnergy : (Gamma → ℂ) → ℝ) (C : ℝ) : Prop :=
  ∀ f : Gamma → ℂ, (∑ x : Gamma, f x) = 0 →
    (finiteTorusQuadratic G f).re ≤ C * inverseEnergy f


end StatMech.FrontierA
