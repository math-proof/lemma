/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/StandardFormBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Prop30_6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Prop30_6
import Mathlib.LinearAlgebra.Matrix.BilinearForm


noncomputable section

set_option autoImplicit false

namespace SymmetricBilinearForms

open Finset

/-- Linear isomorphism `(Fin a → F₂) × (Fin b → Fin 2 → F₂) ≃ₗ
Fin (a + 2 b) → F₂` that interleaves the two factors as in
`standardFormF2`: indices `< a` come from the first factor, and indices
`a + 2k + r` (with `r ∈ {0,1}`) come from the `r`-th coordinate of the
`k`-th block in the second factor. Bridges the abstract product
presentation of Proposition 30.6 with the concrete matrix presentation
`standardFormF2 a b`. -/
def prodToFinEquiv (a b : ℕ) :
    ((Fin a → ZMod 2) × (Fin b → Fin 2 → ZMod 2)) ≃ₗ[ZMod 2] (Fin (a + 2 * b) → ZMod 2) where
  toFun := fun ⟨f, g⟩ => fun i =>
    if h : i.val < a then f ⟨i.val, h⟩
    else g ⟨(i.val - a) / 2, by omega⟩ ⟨(i.val - a) % 2, by omega⟩
  map_add' := by
    intro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩; funext i; simp only [Pi.add_apply]; split_ifs <;> rfl
  map_smul' := by
    intro r ⟨f, g⟩; funext i; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> rfl
  invFun := fun h =>
    (fun i => h ⟨i.val, by omega⟩, fun j k => h ⟨a + 2 * j.val + k.val, by omega⟩)
  left_inv := by
    intro ⟨f, g⟩; simp only; show (_, _) = (f, g)
    congr 1
    · funext i; simp only [dif_pos i.isLt]
    · funext j k
      have hlt : ¬ (a + 2 * j.val + k.val) < a := by omega
      simp only [hlt, dite_false]
      show g ⟨(a + 2 * j.val + k.val - a) / 2, _⟩ ⟨(a + 2 * j.val + k.val - a) % 2, _⟩ = g j k
      have h1 : (a + 2 * j.val + k.val - a) / 2 = j.val := by omega
      have h2 : (a + 2 * j.val + k.val - a) % 2 = k.val := by omega
      simp only [h1, h2]
  right_inv := by
    intro h; funext i; simp only
    split_ifs with hlt
    · rfl
    · show h ⟨a + 2 * ((i.val - a) / 2) + (i.val - a) % 2, _⟩ = h i
      have heq : a + 2 * ((i.val - a) / 2) + (i.val - a) % 2 = i.val := by omega
      simp only [heq]

end SymmetricBilinearForms
end
