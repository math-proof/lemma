import Mathlib
import sympy.Basic
import Theorem.NumberTheory.ContinuedFractions.LagrangePeriodic.Part5
open MetaMathlibExt


namespace MetaMathlibExt

/--
[cfXi_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma cfXi_zero (x : ℝ) : cfXi x 0 = x :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[irr_fract](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma irr_fract (y : ℝ) (hy : Irrational y) : Irrational (Int.fract y) := by
  unfold Irrational
  intro hmem
  obtain ⟨q, hq⟩ := hmem
  apply hy
  exact ⟨(⌊y⌋ : ℚ) + q, by
    push_cast
    rw [hq]
    exact Int.floor_add_fract y⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fract_cfXi_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma fract_cfXi_ne (x : ℝ) (hx : Irrational x) (n : ℕ) :
  Int.fract (cfXi x n) ≠ 0 := by
  intro h0
  apply (irr_cfXi x hx n)
  exact ⟨(⌊cfXi x n⌋ : ℚ), by
    push_cast
    have h1 := Int.floor_add_fract (cfXi x n)
    rw [h0, add_zero] at h1
    exact h1⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fract_cfXi_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma fract_cfXi_pos (x : ℝ) (hx : Irrational x) (n : ℕ) :
  0 < Int.fract (cfXi x n) :=
  lt_of_le_of_ne' (Int.fract_nonneg _) (fract_cfXi_ne x hx n)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fract_cfXi_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma fract_cfXi_lt_one (x : ℝ) (_hx : Irrational x) (n : ℕ) :
  Int.fract (cfXi x n) < 1 :=
  Int.fract_lt_one _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[one_lt_cfXi_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma one_lt_cfXi_succ (x : ℝ) (hx : Irrational x) (n : ℕ) :
  1 < cfXi x (n + 1) :=
  (one_lt_inv₀ (fract_cfXi_pos x hx n)).mpr (fract_cfXi_lt_one x hx n)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[floor_cfXi_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma floor_cfXi_ge_one (x : ℝ) (hx : Irrational x) (n : ℕ) :
  1 ≤ ⌊cfXi x (n + 1)⌋ := by
  rw [Int.le_floor]
  exact_mod_cast le_of_lt (one_lt_cfXi_succ x hx n)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[minpoly_coeff_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma minpoly_coeff_two (x : ℝ) (hint : IsIntegral ℚ x)
  (hdeg : (minpoly ℚ x).natDegree = 2) : (minpoly ℚ x).coeff 2 = 1 := by
  have hmo := minpoly.monic hint
  have h2 := hmo.coeff_natDegree
  rwa [hdeg] at h2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cfP_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma cfP_zero (x : ℝ) : cfP x 0 = 1 :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cfP_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma cfP_one (x : ℝ) : cfP x 1 = ⌊x⌋ :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cfP_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma cfP_add_two (x : ℝ) (n : ℕ) : cfP x (n + 2)
  = ⌊cfXi x (n + 1)⌋ * cfP x (n + 1) + cfP x n :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cfQ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma cfQ_zero (x : ℝ) : cfQ x 0 = 0 :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cfQ_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma cfQ_one (x : ℝ) : cfQ x 1 = 1 :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cfQ_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma cfQ_add_two (x : ℝ) (n : ℕ) : cfQ x (n + 2)
  = ⌊cfXi x (n + 1)⌋ * cfQ x (n + 1) + cfQ x n :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cfDet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma cfDet (x : ℝ) (n : ℕ) :
  cfP x (n + 1) * cfQ x n - cfP x n * cfQ x (n + 1) = (-1) ^ (n + 1) := by
  induction n with
  | zero =>
    change cfP x 1 * cfQ x 0 - cfP x 0 * cfQ x 1 = (-1) ^ (0 + 1)
    rw [cfP_one, cfP_zero, cfQ_one, cfQ_zero]
    norm_num
  | succ n ih =>
    have e : n + 1 + 1 = n + 2 := by omega
    rw [e, cfP_add_two x n, cfQ_add_two x n]
    linear_combination -ih

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cfQ_nonneg_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma cfQ_nonneg_pos (x : ℝ) (hx : Irrational x) (n : ℕ) :
  0 ≤ cfQ x n ∧ 1 ≤ cfQ x (n + 1) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [cfQ_zero]
    · change (1 : ℤ) ≤ cfQ x 1
      rw [cfQ_one]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨zero_le_one.trans h2, ?_⟩
    have e : n + 1 + 1 = n + 2 := by omega
    rw [e, cfQ_add_two x n]
    have ha1 := floor_cfXi_ge_one x hx n
    have hmul : (1 : ℤ) ≤ ⌊cfXi x (n + 1)⌋ * cfQ x (n + 1) :=
      one_le_mul_of_one_le_of_one_le ha1 h2
    linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[triC_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma triC_succ (a b c : ℤ) (x : ℝ) (n : ℕ) :
  triC a b c x (n + 1) = triA a b c x n :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[triA_cast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma triA_cast (a b c : ℤ) (x : ℝ) (n : ℕ) : ((triA a b c x n : ℤ) : ℝ)
  = (a : ℝ) * (cfP x (n + 1) : ℝ) ^ 2 + (b : ℝ) * (cfP x (n + 1) : ℝ)
    * (cfQ x (n + 1) : ℝ) + (c : ℝ) * (cfQ x (n + 1) : ℝ) ^ 2 := by
  simp only [triA]
  push_cast
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[triB_cast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma triB_cast (a b c : ℤ) (x : ℝ) (n : ℕ) : ((triB a b c x n : ℤ) : ℝ)
  = 2 * (a : ℝ) * (cfP x (n + 1) : ℝ) * (cfP x n : ℝ)
    + (b : ℝ) * ((cfP x (n + 1) : ℝ) * (cfQ x n : ℝ)
      + (cfP x n : ℝ) * (cfQ x (n + 1) : ℝ))
    + 2 * (c : ℝ) * (cfQ x (n + 1) : ℝ) * (cfQ x n : ℝ) := by
  simp only [triB]
  push_cast
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[triC_cast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma triC_cast (a b c : ℤ) (x : ℝ) (n : ℕ) : ((triC a b c x n : ℤ) : ℝ)
  = (a : ℝ) * (cfP x n : ℝ) ^ 2 + (b : ℝ) * (cfP x n : ℝ) * (cfQ x n : ℝ)
    + (c : ℝ) * (cfQ x n : ℝ) ^ 2 := by
  simp only [triC]
  push_cast
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[triA_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma triA_ne (x : ℝ) (hx : Irrational x) (a b c : ℤ) (n : ℕ)
  (noroot : ∀ q : ℚ, (a : ℝ) * (((q : ℚ)) : ℝ) ^ 2 + (b : ℝ) * (((q : ℚ)) : ℝ)
    + (c : ℝ) ≠ 0) :
  triA a b c x n ≠ 0 := by
  intro hA
  obtain ⟨hQ0, hQ1⟩ := cfQ_nonneg_pos x hx n
  have hQ' : (cfQ x (n + 1) : ℚ) ≠ 0 := by
    have hne : cfQ x (n + 1) ≠ 0 := by omega
    exact_mod_cast hne
  have htri : ((triA a b c x n : ℤ) : ℚ) = 0 := by exact_mod_cast hA
  set q : ℚ := (cfP x (n + 1) : ℚ) / (cfQ x (n + 1) : ℚ) with hq
  have hfactor : ((triA a b c x n : ℤ) : ℚ)
    = (cfQ x (n + 1) : ℚ) ^ 2 * ((a : ℚ) * q ^ 2 + (b : ℚ) * q + (c : ℚ)) := by
    rw [hq]
    simp only [triA]
    push_cast
    field_simp
  rw [htri] at hfactor
  have hQ2 : (cfQ x (n + 1) : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hQ'
  have h0 : (a : ℚ) * q ^ 2 + (b : ℚ) * q + (c : ℚ) = 0 :=
    (mul_eq_zero.mp hfactor.symm).resolve_left hQ2
  have h0R : (a : ℝ) * (((q : ℚ)) : ℝ) ^ 2 + (b : ℝ) * (((q : ℚ)) : ℝ)
    + (c : ℝ) = 0 := by
    exact_mod_cast h0
  exact noroot q h0R

end MetaMathlibExt

namespace MetaMathlibExt

/--
[triDisc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma triDisc (a b c : ℤ) (x : ℝ) (n : ℕ) :
  (triB a b c x n) ^ 2 - 4 * (triA a b c x n) * (triC a b c x n)
    = (b ^ 2 - 4 * a * c)
      * (cfP x (n + 1) * cfQ x n - cfP x n * cfQ x (n + 1)) ^ 2 := by
  simp only [triA, triB, triC]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cfDet_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma cfDet_sq (x : ℝ) (n : ℕ) :
  (cfP x (n + 1) * cfQ x n - cfP x n * cfQ x (n + 1)) ^ 2 = 1 := by
  rw [cfDet, ← pow_mul]
  exact Even.neg_one_pow ⟨n + 1, by ring⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[triA_eq_form](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma triA_eq_form (x : ℝ) (a b c : ℤ) (n : ℕ)
  (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0)
  (F : ℝ) (hF : F = ((cfQ x (n + 1) : ℤ) : ℝ) * x - ((cfP x (n + 1) : ℤ) : ℝ)) :
  ((triA a b c x n : ℤ) : ℝ)
    = (a : ℝ) * F ^ 2 - F * ((cfQ x (n + 1) : ℤ) : ℝ)
      * (2 * (a : ℝ) * x + (b : ℝ)) := by
  have hP : ((cfP x (n + 1) : ℤ) : ℝ)
    = ((cfQ x (n + 1) : ℤ) : ℝ) * x - F := by rw [hF]; ring
  rw [triA_cast]
  linear_combination ((cfQ x (n + 1) : ℤ) : ℝ) ^ 2 * hquad
    + ((a : ℝ) * (((cfP x (n + 1) : ℤ) : ℝ) + ((cfQ x (n + 1) : ℤ) : ℝ) * x - F)
      + (b : ℝ) * ((cfQ x (n + 1) : ℤ) : ℝ)) * hP

end MetaMathlibExt

namespace MetaMathlibExt

/--
[triB_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma triB_sq (x : ℝ) (a b c : ℤ) (n : ℕ) :
  ((triB a b c x n : ℤ) : ℝ) ^ 2
    = ((b ^ 2 - 4 * a * c : ℤ) : ℝ)
      + 4 * ((triA a b c x n : ℤ) : ℝ) * ((triC a b c x n : ℤ) : ℝ) := by
  have hdisc : ((triB a b c x n : ℤ) : ℝ) ^ 2
    - 4 * ((triA a b c x n : ℤ) : ℝ) * ((triC a b c x n : ℤ) : ℝ)
    = ((b ^ 2 - 4 * a * c : ℤ) : ℝ)
      * ((((cfP x (n + 1) * cfQ x n - cfP x n * cfQ x (n + 1) : ℤ))) : ℝ) ^ 2 := by
    exact_mod_cast triDisc a b c x n
  have hdet : ((((cfP x (n + 1) * cfQ x n - cfP x n * cfQ x (n + 1) : ℤ))) : ℝ) ^ 2
    = 1 := by
    exact_mod_cast cfDet_sq x n
  linear_combination hdisc + ((b ^ 2 - 4 * a * c : ℤ) : ℝ) * hdet

end MetaMathlibExt

namespace MetaMathlibExt

/--
[partDens_shift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma partDens_shift (v : ℝ) (k : ℕ) :
  (GenContFract.of v).partDens.get? (k + 1)
    = (GenContFract.of (Int.fract v)⁻¹).partDens.get? k := by
  change (Stream'.Seq.map GenContFract.Pair.b (GenContFract.of v).s).get? (k + 1)
    = (Stream'.Seq.map GenContFract.Pair.b
      (GenContFract.of (Int.fract v)⁻¹).s).get? k
  rw [Stream'.Seq.map_get?, Stream'.Seq.map_get?, GenContFract.of_s_succ]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[minpoly_eq_form](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma minpoly_eq_form (x : ℝ) (hint : IsIntegral ℚ x)
  (hdeg : (minpoly ℚ x).natDegree = 2) :
  minpoly ℚ x = Polynomial.X ^ 2 + Polynomial.C ((minpoly ℚ x).coeff 1) * Polynomial.X
    + Polynomial.C ((minpoly ℚ x).coeff 0) := by
  conv_lhs => rw [Polynomial.as_sum_range (minpoly ℚ x), hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  rw [minpoly_coeff_two x hint hdeg, Polynomial.C_1, one_mul]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[eval_minpoly_at_rat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma eval_minpoly_at_rat (x : ℝ) (hint : IsIntegral ℚ x)
  (hdeg : (minpoly ℚ x).natDegree = 2) (q : ℚ) :
  (minpoly ℚ x).eval q =
    q ^ 2 + (minpoly ℚ x).coeff 1 * q + (minpoly ℚ x).coeff 0 := by
  conv_lhs => rw [minpoly_eq_form x hint hdeg]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[aeval_minpoly_at_real](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma aeval_minpoly_at_real (x : ℝ) (hint : IsIntegral ℚ x)
  (hdeg : (minpoly ℚ x).natDegree = 2) :
  x ^ 2 + ((minpoly ℚ x).coeff 1 : ℝ) * x + ((minpoly ℚ x).coeff 0 : ℝ) = 0 := by
  have h0 := minpoly.aeval ℚ x
  rw [minpoly_eq_form x hint hdeg] at h0
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h0
  exact h0

end MetaMathlibExt

namespace MetaMathlibExt

/--
[quad_int_of_minpoly](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
with no rational root. -/
private lemma quad_int_of_minpoly (x : ℝ) (hint : IsIntegral ℚ x)
  (hdeg : (minpoly ℚ x).natDegree = 2) :
  ∃ a b c : ℤ, a ≠ 0 ∧ (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0
    ∧ ∀ q : ℚ, (a : ℝ) * (((q : ℚ)) : ℝ) ^ 2 + (b : ℝ) * (((q : ℚ)) : ℝ)
      + (c : ℝ) ≠ 0 := by
  set B := (minpoly ℚ x).coeff 1 with hB
  set C := (minpoly ℚ x).coeff 0 with hC
  have hBC : x ^ 2 + (B : ℝ) * x + (C : ℝ) = 0 := aeval_minpoly_at_real x hint hdeg
  have hnoroot : ∀ q : ℚ, q ^ 2 + B * q + C ≠ 0 := by
    intro q hq
    have hroot : (minpoly ℚ x).IsRoot q := by
      change (minpoly ℚ x).eval q = 0
      rwa [eval_minpoly_at_rat x hint hdeg]
    have hirr := minpoly.irreducible hint
    have hdeg1 := Polynomial.degree_eq_one_of_irreducible_of_root hirr hroot
    have hnat : (minpoly ℚ x).natDegree = 1 :=
      Polynomial.natDegree_eq_of_degree_eq_some hdeg1
    omega
  set a : ℤ := (B.den : ℤ) * C.den with ha_def
  set b : ℤ := B.num * C.den with hb_def
  set c : ℤ := C.num * B.den with hc_def
  have hdenB : B.den ≠ 0 := Rat.den_nz B
  have hdenC : C.den ≠ 0 := Rat.den_nz C
  have hposB : (0 : ℤ) < B.den := by exact_mod_cast Nat.pos_of_ne_zero hdenB
  have hposC : (0 : ℤ) < C.den := by exact_mod_cast Nat.pos_of_ne_zero hdenC
  have ha : a ≠ 0 := ne_of_gt (mul_pos hposB hposC)
  have hBB : B * (B.den : ℚ) = (B.num : ℚ) := Rat.mul_den_eq_num B
  have hCC : C * (C.den : ℚ) = (C.num : ℚ) := Rat.mul_den_eq_num C
  have hDB : (a : ℚ) * B = (b : ℚ) := by
    rw [ha_def, hb_def]
    push_cast
    linear_combination (C.den : ℚ) * hBB
  have hDC : (a : ℚ) * C = (c : ℚ) := by
    rw [ha_def, hc_def]
    push_cast
    linear_combination (B.den : ℚ) * hCC
  have hDBR : (a : ℝ) * (B : ℝ) = (b : ℝ) := by exact_mod_cast hDB
  have hDCR : (a : ℝ) * (C : ℝ) = (c : ℝ) := by exact_mod_cast hDC
  have heq : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0 := by
    have hcast : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ)
      = (a : ℝ) * (x ^ 2 + (B : ℝ) * x + (C : ℝ)) := by
      rw [← hDBR, ← hDCR]; ring
    rw [hcast, hBC, mul_zero]
  refine ⟨a, b, c, ha, heq, ?_⟩
  intro q hq
  apply hnoroot q
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have h0 : (a : ℚ) * q ^ 2 + (b : ℚ) * q + (c : ℚ) = 0 := by exact_mod_cast hq
  have hQ : (a : ℚ) * (q ^ 2 + B * q + C)
    = (a : ℚ) * q ^ 2 + (b : ℚ) * q + (c : ℚ) := by
    rw [mul_add, mul_add, ← mul_assoc, hDB, hDC]
  have hX : (a : ℚ) * (q ^ 2 + B * q + C) = 0 := by rw [hQ]; exact h0
  exact (mul_eq_zero.mp hX).resolve_left haQ

end MetaMathlibExt

namespace MetaMathlibExt

/--
[triPoly_coeff_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma triPoly_coeff_two (A B C : ℝ) : (triPoly A B C).coeff 2 = A := by
  simp [triPoly]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[triPoly_eval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma triPoly_eval (A B C : ℝ) (y : ℝ) :
  (triPoly A B C).eval y = A * y ^ 2 + B * y + C := by
  simp only [triPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[triple_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma triple_mem_box (a b c : ℤ) (x : ℝ) (M K : ℕ)
  (hA : ∀ n, (triA a b c x n).natAbs ≤ M)
  (hB : ∀ n, (triB a b c x n).natAbs ≤ K)
  (hC : ∀ n, (triC a b c x n).natAbs ≤ M)
  (n : ℕ) :
  (triA a b c x n, (triB a b c x n, triC a b c x n)) ∈ triBox M K := by
  have gA := hA n
  have gB := hB n
  have gC := hC n
  simp only [triBox, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩ <;> omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[triU_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma triU_finite (M K : ℕ) : (triU M K).Finite := by
  simp only [triU]
  refine Set.Finite.biUnion (Finset.finite_toSet _) (fun t ht => ?_)
  have hne : t.1 ≠ 0 :=
    (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).2
  have hA : ((t.1 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hne
  apply Polynomial.finite_setOfPred_isRoot
  intro hz
  have h0 : (triPoly ((t.1 : ℤ) : ℝ) ((t.2.1 : ℤ) : ℝ) ((t.2.2 : ℤ) : ℝ)).coeff 2
    = 0 := by simp [hz]
  rw [triPoly_coeff_two] at h0
  exact hA h0

end MetaMathlibExt

namespace MetaMathlibExt

/--
[quad_irrational](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma quad_irrational (x : ℝ) (hint : IsIntegral ℚ x)
  (hdeg : (minpoly ℚ x).natDegree = 2) : Irrational x := by
  obtain ⟨a, b, c, ha, heq, hnoroot⟩ := quad_int_of_minpoly x hint hdeg
  intro hmem
  obtain ⟨q, hq⟩ := hmem
  apply hnoroot q
  rwa [← hq] at heq

end MetaMathlibExt

/--
[continuedFractionEventuallyPeriodic_of_isRealQuadraticIrrational](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean)
-/
@[path]
private lemma continuedFractionEventuallyPeriodic_of_isRealQuadraticIrrational_eq
  {x : ℝ}
-- given
  (h : IsRealQuadraticIrrational x) :
-- imply
  ContinuedFractionEventuallyPeriodic x := by
-- proof
  apply MetaMathlibExt.continuedFractionEventuallyPeriodic_of_isRealQuadraticIrrational x h


-- created on 2026-10-20
-- updated on 2026-10-23
