import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[IsAlgClosed_exists_units_pow_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsAlgClosed_exists_units_pow_eq.lean)
-/
@[path]
private lemma main
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  {n : ℕ}
  (x : Ωˣ)
  -- given
  (hn : 0 < n) :
  -- imply
  ∃ y : Ωˣ, y ^ n = x := by
  -- proof
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : Ω) hn
  have hz0 : z ≠ 0 := by
    rintro rfl
    apply x.ne_zero (by rw [← hz, zero_pow hn.ne'])
  refine ⟨Units.mk0 z hz0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])⟩


-- created on 2026-10-20
