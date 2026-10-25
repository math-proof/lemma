/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.List.FinRange
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Def.Combinatorics.BellPermutationsSecondKind


namespace MetaMathlibExt

/-! ## Every RGF is subdiagonal -/

theorem rgf_subdiag {n : ℕ} {f : Fin n → Fin n} (hf : IsRGF f) : Subdiag f := by
  intro i
  by_contra h
  simp only [not_le] at h
  have hle : (f i).val ≤ i.val → False := by omega
  apply hle
  classical
  have inj : ∀ x : Fin ((f i).val), ∃ i₀ : Fin n, i₀.val < i.val ∧ f i₀ = ⟨x.val, by omega⟩ := by
    intro x
    exact hf i ⟨x.val, by omega⟩ (by simp)
  choose g hg1 hg2 using inj
  have ginj : Function.Injective (fun x : Fin ((f i).val) => (⟨(g x).val, hg1 x⟩ : Fin i.val)) := by
    intro a b hab
    simp only [Fin.mk.injEq] at hab
    have hgab : g a = g b := Fin.ext hab
    have hval : (⟨a.val, by omega⟩ : Fin n) = ⟨b.val, by omega⟩ := by
      rw [← hg2 a, ← hg2 b, hgab]
    exact Fin.ext (by simpa using congrArg Fin.val hval)
  have := Fintype.card_le_of_injective _ ginj
  simpa using this

/-! ## Contiguity: the value set of an RGF is an initial segment -/

theorem downward_closed_card {n : ℕ} (s : Finset (Fin n))
    (hdc : ∀ v w : Fin n, v ∈ s → w.val < v.val → w ∈ s) (v : Fin n) :
    v ∈ s ↔ v.val < s.card := by
  constructor
  · intro hv
    have hsub : Finset.Iic v ⊆ s := by
      intro w hw
      rw [Finset.mem_Iic, Fin.le_def] at hw
      rcases lt_or_eq_of_le hw with h | h
      · exact hdc v w hv h
      · have : w = v := Fin.ext h
        rwa [this]
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hlt
    by_contra hv
    have hsub : s ⊆ Finset.Iio v := by
      intro w hw
      rw [Finset.mem_Iio, Fin.lt_def]
      rcases lt_trichotomy w.val v.val with h | h | h
      · exact h
      · have hwv : w = v := Fin.ext h
        exact absurd (hwv ▸ hw) hv
      · exact absurd (hdc w v hw h) hv
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

theorem rgf_mem_image {n : ℕ} {g : Fin n → Fin n} (hg : IsRGF g) (v : Fin n) :
    v ∈ Finset.univ.image g ↔ v.val < numVals g := by
  apply downward_closed_card
  intro a b ha hab
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha ⊢
  obtain ⟨i, hi⟩ := ha
  obtain ⟨i₀, _, hi₀⟩ := hg i b (by rw [hi]; exact hab)
  exact ⟨i₀, hi₀⟩

theorem numVals_le {n : ℕ} (g : Fin n → Fin n) : numVals g ≤ n := by
  unfold numVals
  calc (Finset.univ.image g).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp

end MetaMathlibExt
