import Mathlib
import sympy.Basic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Formula23SeriesPair

/--
[hzE](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry2Formula23SeriesPair.lean)
-/
@[path]
private lemma hzE (z : ℂ) (hz : ∀ n : ℕ, z ≠ -((n : ℂ) + 1)) (r : ℕ) :
  (z + 1 + (r : ℂ)) ≠ 0 := by
  intro h
  apply hz r
  linear_combination h

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Formula23SeriesPair

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Formula23SeriesPair

/--
[ramanujan_part1_ch3_entry2_formula23_series_pair](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry2Formula23SeriesPair.lean)
-/
@[path]
lemma ramanujan_part1_ch3_entry2_formula23_series_pair
  {x z : ℂ}
-- given
  (hz : ∀ n : ℕ, z ≠ -((n : ℂ) + 1)) :
-- imply
  HasSum (fun j : ℕ => (x ^ (j + 1) / ∏ i ∈ Finset.range (j + 1), (z + ((i : ℂ) + 1)),
    (-1 : ℂ) ^ j * x ^ (j + 1) / ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ))))
    (Complex.exp x * ∑' j : ℕ,
    ((-1 : ℂ) ^ j * x ^ (j + 1) / ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ))),
    ∑' j : ℕ, ((-1 : ℂ) ^ j * x ^ (j + 1) / ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ)))) := by
-- proof
  have hE := Entry2.ramanujan_part1_ch3_entry2 (-x) (z + 1) (hzE z hz)
  have hR := Entry2Rightsummable.ramanujan_part1_ch3_entry2_rightsummable (-x) (z + 1) (hzE z hz)
  -- Entry 2 left summand at `(-x, z+1)` is the negation of our right summand.
  have hBE : ∀ j : ℕ, (((-1 : ℂ) ^ j * x ^ (j + 1)) /
    ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ)))
    = -(((-x) ^ (j + 1)) / ((z + 1 + (j : ℂ)) * (Nat.factorial j : ℂ))) := by
    intro j
    have h1 : (-x : ℂ) ^ (j + 1) = -(((-1 : ℂ) ^ j) * x ^ (j + 1)) := by
      rw [show (-x : ℂ) = (-1) * x from by ring, mul_pow, pow_succ]
      ring
    have h2 : (z + 1 + (j : ℂ)) = (z + ((j : ℂ) + 1)) := by ring
    rw [h1, h2]
    ring
  -- Entry 2 right summand at `(-x, z+1)` is the negation of our left summand.
  have h21 : ∀ j : ℕ, (-1 : ℂ) ^ (2 * j + 1) = -1 := by
    intro j
    rw [pow_succ]
    have hsq : (-1 : ℂ) ^ (2 * j) = 1 := by
      rw [show 2 * j = j + j from by ring, pow_add, ← mul_pow,
        show ((-1 : ℂ) * (-1)) = 1 from by ring, one_pow]
    rw [hsq, one_mul]
  have hCE : ∀ j : ℕ, (x ^ (j + 1) /
    ∏ i ∈ Finset.range (j + 1), (z + ((i : ℂ) + 1)))
    = -(((-1 : ℂ) ^ j * (-x) ^ (j + 1)) /
      ∏ k ∈ Finset.range (j + 1), (z + 1 + (k : ℂ))) := by
    intro j
    have h1 : (-1 : ℂ) ^ j * (-x) ^ (j + 1) = -(x ^ (j + 1)) := by
      rw [show (-x : ℂ) = (-1) * x from by ring, mul_pow, ← mul_assoc, ← pow_add,
        show j + (j + 1) = 2 * j + 1 from by ring, h21 j]
      ring
    have hP : (∏ k ∈ Finset.range (j + 1), (z + 1 + (k : ℂ)))
      = ∏ i ∈ Finset.range (j + 1), (z + ((i : ℂ) + 1)) :=
      Finset.prod_congr rfl (fun i _ => by ring)
    rw [h1, hP]
    ring
  have hBright : HasSum (fun j : ℕ => (-1 : ℂ) ^ j * x ^ (j + 1) /
    ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ)))
    (-(Complex.exp (-x) * ∑' j : ℕ, ((-1 : ℂ) ^ j * (-x) ^ (j + 1) /
      ∏ k ∈ Finset.range (j + 1), (z + 1 + (k : ℂ))))) :=
    hE.neg.congr_fun (fun j => hBE j)
  have hB := hBright.summable
  have hBsum := hB.hasSum
  have hS : (∑' j : ℕ, ((-1 : ℂ) ^ j * x ^ (j + 1) /
    ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ))))
    = -(Complex.exp (-x) * ∑' j : ℕ, ((-1 : ℂ) ^ j * (-x) ^ (j + 1) /
      ∏ k ∈ Finset.range (j + 1), (z + 1 + (k : ℂ)))) :=
    hBsum.unique hBright
  have hCneg : HasSum (fun j : ℕ => x ^ (j + 1) /
    ∏ i ∈ Finset.range (j + 1), (z + ((i : ℂ) + 1)))
    (-∑' j : ℕ, ((-1 : ℂ) ^ j * (-x) ^ (j + 1) /
      ∏ k ∈ Finset.range (j + 1), (z + 1 + (k : ℂ)))) :=
    hR.hasSum.neg.congr_fun (fun j => hCE j)
  have hC := hCneg.summable
  have hT : (∑' j : ℕ, x ^ (j + 1) /
    ∏ i ∈ Finset.range (j + 1), (z + ((i : ℂ) + 1)))
    = -∑' j : ℕ, ((-1 : ℂ) ^ j * (-x) ^ (j + 1) /
      ∏ k ∈ Finset.range (j + 1), (z + 1 + (k : ℂ))) :=
    hC.hasSum.unique hCneg
  have hexp : Complex.exp x * Complex.exp (-x) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hval : Complex.exp x * (∑' j : ℕ, ((-1 : ℂ) ^ j * x ^ (j + 1) /
    ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ))))
    = ∑' j : ℕ, x ^ (j + 1) / ∏ i ∈ Finset.range (j + 1), (z + ((i : ℂ) + 1)) := by
    rw [hS, hT, mul_neg, ← mul_assoc, hexp, one_mul]
  have hCsum : HasSum (fun j : ℕ => x ^ (j + 1) /
    ∏ i ∈ Finset.range (j + 1), (z + ((i : ℂ) + 1)))
    (Complex.exp x * ∑' j : ℕ, ((-1 : ℂ) ^ j * x ^ (j + 1) /
      ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ)))) := by
    rwa [hval]
  exact HasSum.prodMk hCsum hBsum

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Formula23SeriesPair


-- created on 2026-10-20
-- updated on 2026-10-23
