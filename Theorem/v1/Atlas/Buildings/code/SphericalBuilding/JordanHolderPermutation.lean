/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/JordanHolderPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.RefinementDimJumps
import Lemma.Fin.FinrankKSpacesValAdd1.of.IsStrictFlag
set_option maxHeartbeats 800000


namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- For any monotone $g : \{0, \dots, n\} \to \mathbb{N}$ with step increments $\le 1$ and
total increase $g(n) = g(0) + 1$, there is a **unique** index $j$ where $g$ jumps by $1$. -/
theorem existsUnique_step_jump {n : ℕ} (g : Fin (n + 1) → ℕ)
    (hmono : Monotone g)
    (hstep : ∀ j : Fin n, g ⟨j.val + 1, by omega⟩ ≤ g ⟨j.val, by omega⟩ + 1)
    (htotal : g ⟨n, by omega⟩ = g ⟨0, by omega⟩ + 1) :
    ∃! j : Fin n, g ⟨j.val + 1, by omega⟩ = g ⟨j.val, by omega⟩ + 1 := by

  have hexist : ∃ j : Fin n, g ⟨j.val + 1, by omega⟩ = g ⟨j.val, by omega⟩ + 1 := by
    by_contra hall
    push_neg at hall
    have hconst : ∀ (k : ℕ) (hk : k < n + 1), g ⟨k, hk⟩ = g ⟨0, by omega⟩ := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        have hkn : k < n := by omega
        have hmono_step : g ⟨k, by omega⟩ ≤ g ⟨k + 1, hk⟩ :=
          hmono (Fin.mk_le_mk.mpr (by omega))
        have hno_jump := hall ⟨k, hkn⟩
        have hstep_k := hstep ⟨k, hkn⟩
        have hprev := ih (by omega)
        simp only at hno_jump hstep_k hprev
        omega
    have h0 := hconst n (by omega)
    omega

  have huniq : ∀ j j' : Fin n,
      g ⟨j.val + 1, by omega⟩ = g ⟨j.val, by omega⟩ + 1 →
      g ⟨j'.val + 1, by omega⟩ = g ⟨j'.val, by omega⟩ + 1 → j = j' := by
    intro j j' hj hj'
    by_contra h
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne h) with hjlt | hjlt
    · have hge2 : g ⟨j'.val, by omega⟩ ≥ g ⟨j.val + 1, by omega⟩ :=
        hmono (Fin.mk_le_mk.mpr (by omega))
      have hle : g ⟨j'.val + 1, by omega⟩ ≤ g ⟨n, by omega⟩ :=
        hmono (Fin.mk_le_mk.mpr (by omega))
      have hge : g ⟨j.val, by omega⟩ ≥ g ⟨0, by omega⟩ :=
        hmono (Fin.mk_le_mk.mpr (by omega))
      omega
    · have hge2 : g ⟨j.val, by omega⟩ ≥ g ⟨j'.val + 1, by omega⟩ :=
        hmono (Fin.mk_le_mk.mpr (by omega))
      have hle : g ⟨j.val + 1, by omega⟩ ≤ g ⟨n, by omega⟩ :=
        hmono (Fin.mk_le_mk.mpr (by omega))
      have hge : g ⟨j'.val, by omega⟩ ≥ g ⟨0, by omega⟩ :=
        hmono (Fin.mk_le_mk.mpr (by omega))
      omega
  obtain ⟨j, hj⟩ := hexist
  exact ⟨j, hj, fun j' hj' => huniq j' j hj' hj⟩

/-- For each row $i > 0$ of the Schreier refinement of $\sigma$ by $\tau$, there is a unique
column $j$ where the dimension jumps from $\dim(\sigma_{i-1} + \sigma_i \cap \tau_j)$ to
$\dim(\sigma_{i-1} + \sigma_i \cap \tau_{j+1})$ by exactly $1$. -/
theorem existsUnique_jump_col (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (i : Fin (n + 1)) (hi : 0 < i.val) :
    ∃! j : Fin n,
      Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val + 1, by omega⟩) =
      Module.finrank k ↥(schreierCell σ τ i hi ⟨j.val, by omega⟩) + 1 := by
  exact existsUnique_step_jump
    (fun j => Module.finrank k ↥(schreierCell σ τ i hi j))
    (fun _ _ hab => Submodule.finrank_mono (schreierCell_mono σ τ i hi _ _ hab))
    (fun j => schreierCell_finrank_step σ τ hτ i hi j)
    (schreierCell_row_total σ τ hσ i hi)

end GLnBuilding
