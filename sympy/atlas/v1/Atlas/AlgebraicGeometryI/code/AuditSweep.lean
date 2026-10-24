/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AuditSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.BertiniDimensionCount
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.BertiniDimensionCount
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GAGA

set_option linter.unusedVariables false in

example : ∀ {HyperplaneIndex : Type}
    (isBadLocus : HyperplaneIndex → Prop)
    (n d : ℕ) (hdn : d < n)
    (h_incidence_dim : d + (n - d - 1) = n - 1)
    (h_incidence_lt : n - 1 < n)
    (h_bad_proper : {H | isBadLocus H} ≠ Set.univ),
    ∃ H : HyperplaneIndex, ¬ isBadLocus H :=
  @bertini_projective_chevalley_gap

set_option linter.unusedVariables false in
example : ∀ (g : ℕ) (hg : 0 < g),
    ∃ (Λ : AddSubgroup (Fin g → ℂ)),
      Nonempty (Λ ≃+ (Fin (2 * g) → ℤ)) :=
  GAGA.gaga_pic0_is_complex_torus

example (X : SmoothSubvariety) : ∃ H : X.HyperplaneIndex, X.isSmoothSection H :=
  bertini_generic_hyperplane_smooth X
