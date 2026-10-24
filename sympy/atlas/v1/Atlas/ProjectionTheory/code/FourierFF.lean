/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierFF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Data.Fintype.BigOperators

open Finset hiding card
open Fintype (card)
open scoped BigOperators

namespace FourierFF

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}

/-- The standard dot product on `F^d` packaged as an additive homomorphism in the
first argument: `x ↦ ∑ᵢ xᵢ ξᵢ`. -/
noncomputable def dotProd (ξ : Fin d → F) : (Fin d → F) →+ F where
  toFun x := ∑ i, x i * ξ i
  map_zero' := by simp
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]

/-- The Fourier character on `F^d` indexed by frequency `ξ`:
`x ↦ e(⟨x, ξ⟩)`, built from a base additive character `e` on `F`. -/
noncomputable def fourierChar (e : AddChar F ℂ) (ξ : Fin d → F) :
    AddChar (Fin d → F) ℂ :=
  e.compAddMonoidHom (dotProd ξ)

/-- Discrete Fourier transform of `f : F^d → ℂ` at frequency `ξ`:
$$\hat f(\xi) = \sum_{x \in F^d} f(x) \overline{e(\langle x, \xi\rangle)}.$$ -/
noncomputable def dft (e : AddChar F ℂ) (f : (Fin d → F) → ℂ)
    (ξ : Fin d → F) : ℂ :=
  ∑ x, f x * (fourierChar e ξ)⁻¹ x
