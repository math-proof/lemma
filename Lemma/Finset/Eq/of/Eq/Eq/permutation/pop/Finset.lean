import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {p a : ℕ → ℤ}
-- given
  (h₀ : (Finset.range (n + 1)).image p = (Finset.range (n + 1)).image a)
  (h₁ : p n = a n)
  (h₂ : Set.InjOn p ↑(Finset.range (n + 1))) :
-- imply
  (Finset.range n).image p = (Finset.range n).image a := by
-- proof
  have ha : Set.InjOn a ↑(Finset.range (n + 1)) := by
    apply Finset.card_image_iff.mp
    rw [← h₀, Finset.card_image_of_injOn h₂]
  have key : ∀ q : ℕ → ℤ, Set.InjOn q ↑(Finset.range (n + 1)) →
      (Finset.range n).image q = ((Finset.range (n + 1)).image q).erase (q n) := by
    intro q hq
    rw [Finset.range_add_one, Finset.image_insert, Finset.erase_insert]
    intro hm
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hm
    have hk' := Finset.mem_range.mp hk
    have := hq (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))) (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))) he
    omega
  rw [key p h₂, key a ha, h₀, h₁]


-- created on 2026-09-27
