import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry9Odd
open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry9Odd


/--
[entry9_P_closed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry9Odd.lean)
-/
@[path]
private lemma entry9_P_closed_eq
  {a b x z w : ℂ}
  {ε : ℝ}
-- given
  (hεpos : 0 < ε)
  (hεlt : ε < Real.pi)
  (hb : b ≠ 0)
  (h0 : -Real.pi + ε ≤ Complex.arg w)
  (h1 : Complex.arg w ≤ Real.pi - ε)
  (hwpos : 0 < ‖w‖)
  (hz : (z + a) / b = w)
  (hw : ∀ r : ℕ, w + ((r : ℂ) + 1) ≠ 0) :
-- imply
  entry9_P a b x z = Complex.exp (-x) * ∑' (m : ℕ),
    (x ^ (m + 1) / ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1))))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry9Odd.entry9_P_closed a b x z w ε hεpos hεlt hb h0 h1 hwpos hz hw

/--
[ramanujan_part1_ch3_entry9_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry9Odd.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry9_odd_eq
  {a b x : ℂ}
  {ε : ℝ}
  {n : ℕ}
-- given
  (hb : b ≠ 0)
  (hεpos : 0 < ε)
  (hεlt : ε < Real.pi) :
-- imply
  Asymptotics.IsBigO
    (Filter.comap (fun z : ℂ => (z + a) / b)
    (Filter.cocompact ℂ ⊓ Filter.principal {w : ℂ | -Real.pi + ε ≤ Complex.arg w ∧
    Complex.arg w ≤ Real.pi - ε}))
    (fun z : ℂ =>
    (Finset.sum (Finset.range (n + 1))
    (fun k => ((-1 : ℂ) ^ k * generalizedBellGenerating a b x k) / z ^ (k + 1)) -
    entry9_P a b x z))
    (fun z : ℂ => (1 : ℂ) / z ^ (n + 2)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry9Odd.ramanujan_part1_ch3_entry9_odd a b x hb ε hεpos hεlt n


-- created on 2026-10-20
