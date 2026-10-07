import sympy.tensor.index_of
import sympy.sets.sets
import sympy.Basic
import Lemma.Nat.EqIndexGet.of.Lt.InjOnRange


open Nat


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℤ}
  {i j : ℕ}
-- given
  (h : (Finset.range n).image x = Finset.Ico 0 (n : ℤ))
  (hi : i < n)
  (hj : j < n) :
-- imply
  IndexOf.index (i : ℤ)
    (fun k ↦ x (Equiv.swap (IndexOf.index (i : ℤ) x n) (IndexOf.index (j : ℤ) x n) k)) n
    = IndexOf.index (j : ℤ) x n := by
-- proof
  have hsurj : ∀ v ∈ Finset.Ico 0 (n : ℤ), ∃ k < n, x k = v := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (h.symm ▸ hv)
    exact ⟨k, Finset.mem_range.mp hk, rfl⟩
  obtain ⟨a, ha, hxa⟩ := hsurj (i : ℤ) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  obtain ⟨b, hb, hxb⟩ := hsurj (j : ℤ) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  have hc : ((Finset.range n).image x).card = (Finset.range n).card := by
    rw [h, Int.card_Ico, Finset.card_range]
    omega
  have hinj : Set.InjOn x ↑(Finset.range n) := Finset.card_image_iff.mp hc
  rw [← hxa, ← hxb]
  rw [EqIndexGet.of.Lt.InjOnRange x n hinj ha, EqIndexGet.of.Lt.InjOnRange x n hinj hb]
  have hswap_lt : ∀ k ∈ Finset.range n, Equiv.swap a b k ∈ Finset.range n := by
    intro k hk
    obtain rfl | hka := eq_or_ne k a
    ·
      rw [Equiv.swap_apply_left]
      exact Finset.mem_range.mpr hb
    ·
      obtain rfl | hkb := eq_or_ne k b
      ·
        rw [Equiv.swap_apply_right]
        exact Finset.mem_range.mpr ha
      ·
        rw [Equiv.swap_apply_of_ne_of_ne hka hkb]
        exact hk
  have hinj_y : Set.InjOn (fun k ↦ x (Equiv.swap a b k)) ↑(Finset.range n) := by
    intro k1 hk1 k2 hk2 hxy
    exact (Equiv.swap a b).injective
      (hinj (Finset.mem_coe.mpr (hswap_lt k1 hk1)) (Finset.mem_coe.mpr (hswap_lt k2 hk2)) hxy)
  have hyb : x a = (fun k ↦ x (Equiv.swap a b k)) b := by
    simp only [Equiv.swap_apply_right]
  rw [hyb]
  exact EqIndexGet.of.Lt.InjOnRange (fun k ↦ x (Equiv.swap a b k)) n hinj_y hb


-- created on 2026-10-07
