/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RegularElement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import Def.v1.Atlas.TensorCategories.code.RegularElement
open Finset


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

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

end FusionRing
