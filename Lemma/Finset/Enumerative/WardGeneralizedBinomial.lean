import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WardGeneralizedBinomial
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[wardUnitsCarry_eq_div](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WardGeneralizedBinomial.lean)
-/
@[path]
lemma wardUnitsCarry_eq_div
  {b n m : ℕ} :
-- imply
  wardUnitsCarry b n m = (n % b + m % b) / b := by
-- proof
  unfold wardUnitsCarry
  obtain hb | hb := Nat.lt_or_ge 1 b
  · have hn := Nat.mod_lt n (by omega : 0 < b)
    have hm := Nat.mod_lt m (by omega : 0 < b)
    split_ifs with h
    · exact (Nat.div_eq_of_lt_le (by omega) (by omega)).symm
    · exact (Nat.div_eq_of_lt (by omega)).symm
  · rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp [Nat.mod_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wardGeneralizedBinomialCoefficient_eq_prod_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WardGeneralizedBinomial.lean)
-/
@[path]
lemma wardGeneralizedBinomialCoefficient_eq_prod_Icc
  [CommMonoid R]
  {s : ℕ → R}
  {n m : ℕ} :
-- imply
  wardGeneralizedBinomialCoefficient s n m =
      ∏ b ∈ Finset.Icc 2 (n + m), s b ^ ((n % b + m % b) / b) := by
-- proof
  have hset : (Finset.range (n + m + 1)).filter (fun b => 1 < b) = Finset.Icc 2 (n + m) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  simp only [wardGeneralizedBinomialCoefficient, hset, wardUnitsCarry_eq_div]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
