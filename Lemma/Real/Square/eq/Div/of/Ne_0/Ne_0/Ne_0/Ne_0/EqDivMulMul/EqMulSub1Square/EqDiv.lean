import sympy.Basic
open Real


/--
Kepler III algebra: from \(T=\dfrac{2m\pi ab}{J}\), \(b^2=a^2(1-e^2)\) and
\(a(1-e^2)=\dfrac{J^2}{GMm^2}\),
\[
T^2=\frac{4\pi^2 m^2a^2b^2}{J^2}=\frac{4\pi^2m^2a^3}{J^2}\cdot\frac{J^2}{GMm^2}
=\frac{4\pi^2a^3}{GM}.
\]
-/
@[main]
private lemma main
  {T m J G M a b e : ℝ}
-- given
  (hm : m ≠ 0)
  (hJ : J ≠ 0)
  (hG : G ≠ 0)
  (hM : M ≠ 0)
  (hT : T = 2 * m * π * a * b / J)
  (hb : b ^ 2 = a ^ 2 * (1 - e ^ 2))
  (ha : a * (1 - e ^ 2) = J ^ 2 / (G * M * m ^ 2)) :
-- imply
  T ^ 2 = 4 * π ^ 2 * a ^ 3 / (G * M) := by
-- proof
  have h : T ^ 2 = 4 * π ^ 2 * m ^ 2 * a ^ 2 * b ^ 2 / J ^ 2 := by
    rw [hT]
    field_simp [hJ]
    ring
  have h' : a ^ 2 * b ^ 2 = a ^ 3 * (a * (1 - e ^ 2)) := by
    rw [hb]
    ring
  rw [h, mul_assoc (4 * π ^ 2 * m ^ 2) (a ^ 2) (b ^ 2), h', ha]
  field_simp [hm, hJ, hG, hM]


-- created on 2026-09-29