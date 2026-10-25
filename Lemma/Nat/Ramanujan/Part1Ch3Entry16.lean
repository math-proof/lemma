import Mathlib
import sympy.Basic
import Def.NumberTheory.Ramanujan.Part1Ch3Entry16
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry16


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry16

/--
[ramanujan_part1_ch3_entry16](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry16.lean)
-/
@[path]
lemma ramanujan_part1_ch3_entry16
  {a x n : ℂ}
  {r : ℤ}
-- given
  (hx_ne : x ≠ 0)
  (hx_eq : x = a * Complex.log x)
  (ha : ‖a‖ > Real.exp 1 ∨ (a = (Real.exp 1 : ℂ) ∧ r ≤ -2))
  (hn : ∀ k : ℕ, r + (k : ℤ) < 0 → n + (k : ℂ) ≠ 0) :
-- imply
  n * varphi a x r n = varphi a x (r + 1) n - Complex.log x * varphi a x (r + 1) (n + 1) := by
-- proof
  have hkey : n * Entry12.F r n a
    = Entry12.F (r + 1) n a - a⁻¹ * Entry12.F (r + 1) (n + 1) a := by
    rw [Entry12.ramanujan_part1_ch3_entry12 r n a ha hn, one_div]
    ring
  -- Exponential identity
  set L : ℂ := Complex.log x with hL
  have hE1 : a * L = Complex.exp L := by
    rwa [Complex.exp_log hx_ne]
  have hexp : Complex.exp L * Complex.exp (-L) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hainv : a⁻¹ = L * Complex.exp (-L) := by
    apply inv_eq_of_mul_eq_one_right
    calc a * (L * Complex.exp (-L)) = (a * L) * Complex.exp (-L) := by ring
      _ = Complex.exp L * Complex.exp (-L) := by rw [hE1]
      _ = 1 := hexp
  have hE2 : Complex.exp (-(n + 1) * L) = Complex.exp (-L) * Complex.exp (-n * L) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hE : a⁻¹ * Complex.exp (-n * L) = L * Complex.exp (-(n + 1) * L) := by
    rw [hainv, hE2]
    ring
  have hfin : a⁻¹ * Entry12.F (r + 1) (n + 1) a * Complex.exp (-n * L)
    = L * (Entry12.F (r + 1) (n + 1) a * Complex.exp (-(n + 1) * L)) := by
    rw [mul_right_comm, hE]
    ring
  -- Assemble
  unfold varphi
  conv_lhs => rw [← mul_assoc]
  rw [hkey, sub_mul, hfin]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry16


-- created on 2026-10-20
-- updated on 2026-10-23
