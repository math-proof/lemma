/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PerronFrobenius/Assembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.PerronFrobeniusProof.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.PerronFrobeniusProof
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
open FusionRing


section Assembly

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]

noncomputable example : HasPerronFrobeniusProperty ι := inferInstance

noncomputable example (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    Σ' (r : ℝ) (v : ι → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ M.mulVec v = r • v :=
  PerronFrobenius.perronFrobeniusExistence M hM

example (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j)
    (r₁ r₂ : ℝ) (v w : ι → ℝ)
    (hv : ∀ i, 0 < v i) (hev : M.mulVec v = r₁ • v)
    (hw : ∀ i, 0 < w i) (hew : M.mulVec w = r₂ • w) :
    ∃ c : ℝ, ∀ i, w i = c * v i :=
  PerronFrobeniusGeneral.pfUnique_general M hM r₁ r₂ v w hv hev hw hew

noncomputable example (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    PerronFrobenius M :=
  perron_frobenius_pos_matrix M hM

noncomputable example (R : FusionRing ι) : Nonempty R.FPdimData :=
  R.exists_FPdimData

end Assembly
