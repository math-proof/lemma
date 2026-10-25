/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part8
set_option autoImplicit false

open DifferentialFormSpace


/-- A parametrix (pseudo-inverse) for an operator $L$ on the differential form spaces:
$PL = \mathrm{id} + S_{\text{left}}$ and $LP = \mathrm{id} + S_{\text{right}}$ with
smoothing remainders. -/
structure HasParametrixDFS
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [HasSobolevSpaces Ω VF]
    (L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)) where
  P : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  S_left : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  S_right : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  PL_eq : ∀ {p : ℕ} (α : Ω (p + 1)), P (L α) = α + S_left α
  LP_eq : ∀ {p : ℕ} (α : Ω (p + 1)), L (P α) = α + S_right α
  S_left_isSmoothing : IsSmoothing (inst := inst) S_left
  S_right_isSmoothing : IsSmoothing (inst := inst) S_right


/-- A Fredholm operator on differential forms: linear, with a parametrix, having finite
dimensional kernel and cokernel and complemented (closed) range. -/
structure IsFredholm
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)) where
  P : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  S_left : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  S_right : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  PL_eq : ∀ {p : ℕ} (α : Ω (p + 1)), P (L α) = α + S_left α
  LP_eq : ∀ {p : ℕ} (α : Ω (p + 1)), L (P α) = α + S_right α
  ker_contained : ∀ {p : ℕ} (α : Ω (p + 1)),
    L α = 0 → α + S_left α = P (0 : Ω (p + 1))
  L_add : ∀ {p : ℕ} (α β : Ω (p + 1)), L (α + β) = L α + L β
  L_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)), L (r • α) = r • L α
  kernel_finiteDim : ∀ (p : ℕ),
    FiniteDimensional ℝ ↥(LinearMap.ker
      ({ toFun := (L : Ω (p + 1) → Ω (p + 1))
         map_add' := L_add
         map_smul' := L_smul } : Ω (p + 1) →ₗ[ℝ] Ω (p + 1)))
  cokernel_finiteDim : ∀ (p : ℕ),
    FiniteDimensional ℝ (Ω (p + 1) ⧸ LinearMap.range
      ({ toFun := (L : Ω (p + 1) → Ω (p + 1))
         map_add' := L_add
         map_smul' := L_smul } : Ω (p + 1) →ₗ[ℝ] Ω (p + 1)))
  range_complemented : ∀ (p : ℕ),
    ∃ (C : Submodule ℝ (Ω (p + 1))),
      LinearMap.range
        ({ toFun := (L : Ω (p + 1) → Ω (p + 1))
           map_add' := L_add
           map_smul' := L_smul } : Ω (p + 1) →ₗ[ℝ] Ω (p + 1)) ⊔ C = ⊤ ∧
      LinearMap.range
        ({ toFun := (L : Ω (p + 1) → Ω (p + 1))
           map_add' := L_add
           map_smul' := L_smul } : Ω (p + 1) →ₗ[ℝ] Ω (p + 1)) ⊓ C = ⊥

