/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnCommonApartmentUnconditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.JordanHolderFrame.Part2
import Lemma.Fin.JhLine.in.SpacesAddVal1.of.IsStrictFlag.IsStrictFlag
import Lemma.Submodule.Any_LtAndLtAndEqFinrankK_AddFinrankK1.of.LeAddFinrankK2_FinrankK.Lt
import Def.v1.Atlas.Buildings.code.SphericalBuilding.AdaptedBasisProof
import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnCommonApartmentUnconditional.Part2
set_option maxHeartbeats 1600000


namespace GLnBuilding

open Submodule Module

variable {k : Type*} [Field k]


section TauCompatibility

/-- The cardinality $|\mathrm{tauWitness}\ \sigma\ \tau\ j| = j$, by bijectivity of the
jump-column map. -/
theorem card_tauWitness_eq (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag)
    (j : Fin (n + 1)) :
    (tauWitness σ τ hσ hτ j).card = j.val := by
  set f := fun i : Fin n =>
    jumpCol σ τ hσ hτ ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_pos _)
  have hinj : Function.Injective f := jumpCol_injective σ τ hσ hτ
  have hbij : Function.Bijective f := (Finite.injective_iff_bijective).mp hinj
  have h_tw : (tauWitness σ τ hσ hτ j) =
      Finset.univ.filter (fun i : Fin n => (f i).val < j.val) := rfl
  rw [h_tw]

  have hcard_target : (Finset.univ.filter (fun c : Fin n => c.val < j.val)).card = j.val := by
    rw [Fin.card_filter_val_lt]
    exact Nat.min_eq_right (by omega)

  let e : Fin n ≃ Fin n := Equiv.ofBijective f hbij

  have hcard_eq : (Finset.univ.filter (fun i : Fin n => (f i).val < j.val)).card =
      (Finset.univ.filter (fun c : Fin n => c.val < j.val)).card := by

    have : Finset.univ.filter (fun i : Fin n => (f i).val < j.val) =
        Finset.univ.filter (fun i : Fin n => (e i).val < j.val) := rfl
    rw [this]
    rw [show Finset.univ.filter (fun i : Fin n => (e i).val < j.val) =
        (Finset.univ.filter (fun c : Fin n => c.val < j.val)).map e.symm.toEmbedding from by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Equiv.toEmbedding_apply]
      constructor
      · intro h
        exact ⟨e i, h, by simp⟩
      · rintro ⟨c, hc, hci⟩
        have : i = e.symm c := hci.symm
        rw [this]
        simp [hc]]
    simp [Finset.card_map]
  rw [hcard_eq, hcard_target]

/-- The Jordan–Hölder frame is compatible with every $τ.\mathrm{spaces}\ j$, i.e.\
$τ.\mathrm{spaces}\ j = \bigoplus_{i \in \mathrm{tauWitness}\ j} \mathrm{jhLine}\ i$. -/
theorem jordanHolderFrame_compatible_tau (σ τ : CompleteFlag k n)
    (hσ : σ.IsStrictFlag) (hτ : τ.IsStrictFlag) [FiniteDimensional k (Vec k n)]
    (j : Fin (n + 1)) :
    (jordanHolderFrame σ τ hσ hτ).IsCompatible k n (τ.spaces j) := by
  use tauWitness σ τ hσ hτ j
  have hFD : FiniteDimensional k ↥(τ.spaces j) :=
    FiniteDimensional.finiteDimensional_submodule (τ.spaces j)
  symm
  apply biSup_span_singleton_eq_of_le_of_finrank (jhLine_linearIndependent σ τ hσ hτ)
  · apply iSup_le; intro i; apply iSup_le; intro hi
    simp only [tauWitness, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    show k ∙ jhLine σ τ hσ hτ i ≤ τ.spaces j
    rw [Submodule.span_singleton_le_iff_mem]
    exact jhLine_mem_tau_of_le σ τ hσ hτ i j (by omega)
  · rw [hτ j, card_tauWitness_eq]

end TauCompatibility


/-- If $n \le 1$, then $k^n$ has no proper non-zero subspaces. -/
theorem no_proper_nonzero_subspace_of_le_one' {n : ℕ} (hn : n ≤ 1)
    (V : Submodule k (Vec k n)) (hbot : V ≠ ⊥) (htop : V ≠ ⊤) : False := by
  have hpos : 0 < finrank k V := by
    by_contra h
    push_neg at h
    have : finrank k V = 0 := Nat.eq_zero_of_le_zero h
    have := Submodule.finrank_eq_zero.mp this
    exact hbot this
  have hlt : finrank k V < n := by
    have h1 : finrank k ↥V < finrank k ↥(⊤ : Submodule k (Vec k n)) :=
      Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr htop)
    rw [finrank_top] at h1
    rwa [finrank_fin_fun] at h1
  omega

/-- If $n \le 1$, no `SubspaceFlag k n` exists (the chain would require a proper non-zero
subspace, which is impossible). -/
theorem subspaceFlag_empty_of_le_one' {n : ℕ} (hn : n ≤ 1) (σ : SubspaceFlag k n) : False := by
  obtain ⟨V, hV_mem⟩ := List.exists_mem_of_ne_nil _ σ.chain_nonempty
  exact no_proper_nonzero_subspace_of_le_one' hn V (σ.chain_proper V hV_mem).1 (σ.chain_proper V hV_mem).2


end GLnBuilding
