/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/SemidirectExistenceInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.GeometricAlgebra.SemidirectExistence
import Lemma.Fin.IsCompl
import Theorem.v1.Atlas.Buildings.code.GeometricAlgebra.SemidirectExistenceInstance


namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Strong-induction wrapper around `semidirect_existence_compl` that establishes the
`SemidirectExistenceProperty` for any finite-dimensional `V`: the parabolic stabilizer of
a flag admits the Levi-unipotent semidirect decomposition `p = d ∘ u`. -/
instance [FiniteDimensional k V] : SemidirectExistenceProperty k V where
  exists_decomp_linear := by
    intro F F' hopp hlen_pos hcov p hp

    suffices hmain : ∀ (n : ℕ) (F F' : Flag k V),
        Flag.isOppositeFlag F F' →
        F.len = n → (hlen_pos' : 0 < F.len) →
        F.spaces ⟨F.len - 1, by omega⟩ = ⊤ →
        ∀ (p : V ≃ₗ[k] V),
        (∀ i : Fin F.len, (F.spaces i).map p.toLinearMap = F.spaces i) →
        ∃ (d u : V ≃ₗ[k] V),
          (∀ i : Fin F.len, (F.spaces i).map d.toLinearMap = F.spaces i) ∧
          (∀ i : Fin F'.len, (F'.spaces i).map d.toLinearMap = F'.spaces i) ∧
          (∀ i : Fin F.len, (F.spaces i).map u.toLinearMap = F.spaces i) ∧
          (∀ i : Fin F.len, ∀ v ∈ F.spaces i,
            u.toLinearMap v - v ∈
              if h : (i : ℕ) = 0 then (⊥ : Submodule k V)
              else F.spaces ⟨i.val - 1, by omega⟩) ∧
          p.toLinearMap = d.toLinearMap.comp u.toLinearMap by
      exact hmain F.len F F' hopp rfl hlen_pos hcov p hp
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih_strong =>
      intro F F' hopp hlen_n hlen_pos hcov p hp
      by_cases hn1 : n ≤ 1
      · exact semidirect_existence_len_one F F' hopp (by omega) hcov p hp
      · push_neg at hn1
        apply semidirect_existence_inductive_step F F' hopp (by omega) hcov p hp
        intro G G' hGG'_len hGG'_compl hG_lt hG_pos hG_cov q hq
        exact semidirect_existence_compl G G' hGG'_len hGG'_compl hG_pos hG_cov q hq

end GeometricAlgebra
