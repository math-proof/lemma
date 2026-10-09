import Mathlib
import sympy.Basic


/--
[PadicInt_ringHom_eq_ringHom_of_isNilpotent](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PadicInt_ringHom_eq_ringHom_of_isNilpotent.lean)
-/
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime]
  {B : Type u} [CommRing B]
  {f g : ℤ_[p] →+* B}
-- given
  (hB : IsNilpotent (p : B)) :
-- imply
  f = g := by
-- proof
  obtain ⟨n, hn⟩ := hB
  refine RingHom.ext fun x => ?_
  have hx := PadicInt.appr_spec n x
  rw [Ideal.mem_span_singleton] at hx
  obtain ⟨y, hy⟩ := hx
  have hx' : x = (PadicInt.appr x n : ℤ_[p]) + (p : ℤ_[p]) ^ n * y := by rw [← hy]; ring
  rw [hx', map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, map_natCast,
    map_natCast, hn, zero_mul, zero_mul]


-- created on 2026-10-05
