import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProjectionTheory.code.HighFreqMultConv
open Finset Complex BigOperators HighFreqMultConv


namespace HighFreqMultConv

/--
[sum_div_left_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HighFreqMultConv.lean)
-/
@[path]
lemma sum_div_left_eq
  {q : ℕ}
  [NeZero q]
  {g : (ZMod q)ˣ → ℂ}
  {a : (ZMod q)ˣ} :
-- imply
  ∑ b : (ZMod q)ˣ, g (a / b) = ∑ b : (ZMod q)ˣ, g b :=
-- proof
  Fintype.sum_equiv (Equiv.divLeft a) _ _ (fun _ => rfl)

end HighFreqMultConv

namespace HighFreqMultConv

/--
[sum_div_right_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HighFreqMultConv.lean)
-/
@[path]
lemma sum_div_right_eq
  {q : ℕ}
  [NeZero q]
  {g : (ZMod q)ˣ → ℂ}
  {x : (ZMod q)ˣ} :
-- imply
  ∑ i : (ZMod q)ˣ, g (i / x) = ∑ i : (ZMod q)ˣ, g i :=
-- proof
  Fintype.sum_equiv (Equiv.divRight x) _ _ (fun _ => rfl)

end HighFreqMultConv

namespace HighFreqMultConv

/--
[highFreq_mulConvUnits](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HighFreqMultConv.lean)
-/
@[path]
lemma highFreq_mulConvUnits
  {q : ℕ}
  [NeZero q]
  [Fact (Nat.Prime q)]
  {f g : (ZMod q)ˣ → ℂ} :
-- imply
  highFreqUnits q (mulConvUnits q f g) = mulConvUnits q (highFreqUnits q f) (highFreqUnits q g) := by
-- proof
  funext a
  simp only [highFreqUnits, mulConvUnits]
  have hn : (Fintype.card (ZMod q)ˣ : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hga : ∑ b : (ZMod q)ˣ, g (a / b) = ∑ b : (ZMod q)ˣ, g b :=
    sum_div_left_eq q g a
  have hconv : (∑ c : (ZMod q)ˣ, ∑ b : (ZMod q)ˣ, f b * g (c / b)) =
    (∑ b : (ZMod q)ˣ, f b) * (∑ b : (ZMod q)ˣ, g b) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_div_right_eq]
    rw [← Finset.sum_mul]
  rw [hconv]
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, hga, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp_rw [← Finset.sum_mul]
  field_simp
  ring

end HighFreqMultConv


-- created on 2026-10-23
