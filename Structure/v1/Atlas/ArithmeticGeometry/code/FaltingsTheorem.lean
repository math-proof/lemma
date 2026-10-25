/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FaltingsTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finite.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Setoid.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.FaltingsTheorem
open MvPolynomial


structure IrreducibleCurveOverQ where
  n : ℕ
  definingEquations : Set (MvPolynomial (Fin n) ℚ)
  genus : ℕ
  isHomogeneous : ∀ f ∈ definingEquations, ∃ d : ℕ, f.IsHomogeneous d
  isIrreducible : (Ideal.span definingEquations).IsPrime
  isCurve : ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ Ideal.span definingEquations) = 2
  genus_of_plane_curve : definingEquations.ncard = 1 → n = 3 →
    ∃ (d : ℕ) (f : MvPolynomial (Fin n) ℚ),
      f ∈ definingEquations ∧ f.IsHomogeneous d ∧ genus = (d - 1) * (d - 2) / 2

