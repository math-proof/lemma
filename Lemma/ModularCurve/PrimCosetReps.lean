import Mathlib
import Lemma.ModularCurve.PhiGen
import Def.ModularCurve_PrimCosetReps

set_option autoImplicit false

namespace ModularCurve


theorem mem_primCosetReps {N a b d : ℕ} (hN : N ≠ 0) :
    (a, b, d) ∈ primCosetReps N ↔ a * d = N ∧ b < d ∧ Nat.gcd a (Nat.gcd b d) = 1 := by
  simp only [primCosetReps, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨_, had, hbd, hgcd⟩
    exact ⟨had, hbd, hgcd⟩
  · rintro ⟨had, hbd, hgcd⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hN (by simpa using had.symm)
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hN (by simpa using had.symm)
    have haN : a ≤ N := had ▸ Nat.le_mul_of_pos_right a (Nat.pos_of_ne_zero hd0)
    have hdN : d ≤ N := had ▸ Nat.le_mul_of_pos_left d (Nat.pos_of_ne_zero ha0)
    exact ⟨⟨by omega, by omega, by omega⟩, had, hbd, hgcd⟩

section Conjugates

variable {K : Type*} [Field K]


theorem cosetConj_eq (ζ : Kˣ) (J : LaurentSeries K) (a b d : ℕ) [NeZero a] :
    cosetConj ζ J (a, b, d) = cosetSubst ζ a b J := by
  unfold cosetConj
  rw [dif_neg (NeZero.ne a)]

end Conjugates

end ModularCurve
