import sympy.Basic
open Real


/--
Kepler's third law, ratio form: \(T^2=\dfrac{4\pi^2a^3}{GM}\) gives
\(\dfrac{a^3}{T^2}=\dfrac{GM}{4\pi^2}\).
-/
@[path]
private lemma main
  {T G M a : ℝ}
-- given
  (ha : a ≠ 0)
  (hG : G ≠ 0)
  (hM : M ≠ 0)
  (hT : T ^ 2 = 4 * π ^ 2 * a ^ 3 / (G * M)) :
-- imply
  a ^ 3 / T ^ 2 = G * M / (4 * π ^ 2) := by
-- proof
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [hT]
  field_simp [ha, hG, hM, hπ]


-- created on 2026-09-29