/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RegularElement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
open Finset


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- A family of real coefficients `coeffs` is a regular element of a fusion ring
`A` with Frobenius–Perron dimension data `fpd` if it is a simultaneous eigenvector
of left multiplication by every basis object `X` with eigenvalue `fpd.d X`. -/
def IsRegularElement (A : FusionRing ι) (fpd : A.FPdimData) (coeffs : ι → ℝ) : Prop :=
  ∀ (X k : ι), ∑ j : ι, (A.N X j k : ℝ) * coeffs j = fpd.d X * coeffs k

end FusionRing
