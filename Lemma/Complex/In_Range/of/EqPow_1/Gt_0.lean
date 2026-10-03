import Mathlib
import sympy.Basic


/--
[RingHom_mem_range_of_pow_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RingHom_mem_range_of_pow_eq_one.lean)
-/
@[main]
private lemma main
  [Field F] [IsAlgClosed F] [CharZero F]
  {σ : F →+* ℂ}
  {ζ : ℂ}
  {n : ℕ}
-- given
  (hn : 0 < n)
  (hζ : ζ ^ n = 1) :
-- imply
  ζ ∈ σ.range := by
-- proof
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.prim (M := F) (n := n)
  obtain ⟨i, -, hi⟩ := (hζ₀.map_of_injective σ.injective).eq_pow_of_pow_eq_one hζ
  exact ⟨ζ₀ ^ i, by rw [map_pow, hi]⟩


-- created on 2026-10-03
