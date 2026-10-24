/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RegularElement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.FrobeniusPerron
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron

open Finset

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- A family of real coefficients `coeffs` is a regular element of a fusion ring
`A` with Frobenius–Perron dimension data `fpd` if it is a simultaneous eigenvector
of left multiplication by every basis object `X` with eigenvalue `fpd.d X`. -/
def IsRegularElement (A : FusionRing ι) (fpd : A.FPdimData) (coeffs : ι → ℝ) : Prop :=
  ∀ (X k : ι), ∑ j : ι, (A.N X j k : ℝ) * coeffs j = fpd.d X * coeffs k

/-- A regular element of a fusion ring `R`: a positive vector `r` that is absorbed
on both sides by multiplication with eigenvalue equal to the Frobenius–Perron
dimension, and whose Frobenius–Perron norm `∑ d_i · r_i` is positive. -/
structure RegularElement (R : FusionRing ι) (fpd : R.FPdimData) where
  r : ι → ℝ
  r_pos : ∀ i, 0 < r i
  left_absorb : ∀ (X k : ι),
    ∑ j : ι, (R.N X j k : ℝ) * r j = fpd.d X * r k
  right_absorb : ∀ (Y k : ι),
    ∑ j : ι, (R.N j Y k : ℝ) * r j = fpd.d Y * r k
  fpdim_pos : 0 < ∑ i : ι, fpd.d i * r i
