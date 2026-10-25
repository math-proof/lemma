import Mathlib
import sympy.Basic
import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part22
open Polynomial
open scoped CharTwo
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo


namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]


namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ratFunc_ne_zero_of_num_degree_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ratFunc_ne_zero_of_num_degree_gt {r : RatFunc F}
  (hdegree : r.denom.natDegree < r.num.natDegree) : r ≠ 0 := by
  intro hzero
  rw [hzero] at hdegree
  simp at hdegree

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[intDegree_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma intDegree_pow {x : RatFunc F} (hx : x ≠ 0) (n : ℕ) :
  (x ^ n).intDegree = (n : ℤ) * x.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hx) hx, ih]
    push_cast
    ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[intDegree_pow_le_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma intDegree_pow_le_zero {x : RatFunc F} (hx : x.intDegree ≤ 0)
  (n : ℕ) : (x ^ n).intDegree ≤ 0 := by
  by_cases hx0 : x = 0
  · cases n <;> simp [hx0]
  rw [intDegree_pow hx0]
  exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg n) hx

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[intDegree_add_le_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma intDegree_add_le_of_le {x y : RatFunc F} {m : ℤ}
  (hm : 0 ≤ m) (hx : x.intDegree ≤ m) (hy : y.intDegree ≤ m) :
  (x + y).intDegree ≤ m := by
  by_cases hxy : x + y = 0
  · simp [hxy, hm]
  by_cases hy0 : y = 0
  · simpa [hy0] using hx
  exact (RatFunc.intDegree_add_le hy0 hxy).trans (max_le hx hy)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[intDegree_mul_le_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma intDegree_mul_le_of_le {x y : RatFunc F} {m n : ℤ}
  (hmn : 0 ≤ m + n) (hx : x.intDegree ≤ m) (hy : y.intDegree ≤ n) :
  (x * y).intDegree ≤ m + n := by
  by_cases hx0 : x = 0
  · simp [hx0, hmn]
  by_cases hy0 : y = 0
  · simp [hy0, hmn]
  rw [RatFunc.intDegree_mul hx0 hy0]
  exact add_le_add hx hy

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[intDegree_add_eq_left_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma intDegree_add_eq_left_of_lt {x y : RatFunc F}
  (hx0 : x ≠ 0) (hdegree : y.intDegree < x.intDegree) :
  (x + y).intDegree = x.intDegree := by
  by_cases hy0 : y = 0
  · simp [hy0]
  have hsum0 : x + y ≠ 0 := by
    intro hzero
    have hxy : x = -y := by linear_combination hzero
    have hdegrees := congrArg RatFunc.intDegree hxy
    rw [RatFunc.intDegree_neg] at hdegrees
    omega
  apply le_antisymm
  · exact (RatFunc.intDegree_add_le hy0 hsum0).trans
    (max_le le_rfl hdegree.le)
  · have hneg : -y ≠ 0 := neg_ne_zero.mpr hy0
    have hrecover : (x + y) + -y = x := by ring
    have hrecover0 : (x + y) + -y ≠ 0 := by rw [hrecover]; exact hx0
    have hbound := RatFunc.intDegree_add_le hneg hrecover0
    rw [hrecover, RatFunc.intDegree_neg] at hbound
    by_contra hnot
    have hlt : (x + y).intDegree < x.intDegree := lt_of_not_ge hnot
    omega

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[degreeDataAtTwo_of_pointCount_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma degreeDataAtTwo_of_pointCount_bounds (N : ℕ) (hpos : 1 ≤ N) (hle : N ≤ 5) :
  Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData 2 N) := by
  have hcases : N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 := by omega
  obtain rfl | rfl | rfl | rfl | rfl := hcases
  · exact ⟨positiveQuadraticDegreeData 2 1 2 (by norm_num) (by
    intro n
    norm_num [quadraticDegree]
    nlinarith [sq_nonneg (n + 1)])⟩
  · exact ⟨positiveQuadraticDegreeData 2 2 1 (by norm_num) (by
    intro n
    norm_num [quadraticDegree]
    nlinarith [sq_nonneg (2 * n + 1)])⟩
  · exact ⟨positiveQuadraticDegreeData 2 3 0 (by norm_num) (by
    intro n
    norm_num [quadraticDegree]
    nlinarith [sq_nonneg n])⟩
  · exact ⟨positiveQuadraticDegreeData 2 4 (-1) (by norm_num) (by
    intro n
    norm_num [quadraticDegree]
    nlinarith [sq_nonneg (2 * n - 1)])⟩
  · exact ⟨positiveQuadraticDegreeData 2 5 (-2) (by norm_num) (by
    intro n
    norm_num [quadraticDegree]
    nlinarith [sq_nonneg (n - 1)])⟩

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[degreeDataAtFour_of_pointCount_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma degreeDataAtFour_of_pointCount_bounds (N : ℕ) (hpos : 1 ≤ N) (hle : N ≤ 9) :
  Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData 4 N) := by
  let a : ℤ := 5 - N
  have hNpos : (1 : ℤ) ≤ N := by exact_mod_cast hpos
  have hNle : (N : ℤ) ≤ 9 := by exact_mod_cast hle
  have hdisc : a ^ 2 ≤ 16 := by
    dsimp only [a]
    nlinarith [mul_nonneg (sub_nonneg.mpr hNpos) (sub_nonneg.mpr hNle)]
  refine ⟨nonnegativeQuadraticDegreeData 4 N a (by simp [a]) ?_ ?_⟩
  · intro n
    norm_num [quadraticDegree]
    nlinarith [sq_nonneg (2 * n + a)]
  · intro n hn hn1
    norm_num [quadraticDegree] at hn hn1
    nlinarith [sq_nonneg (2 * n + a)]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

/--
[manin_degree_data_of_card_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
lemma manin_degree_data_of_card_eq_two
  {F : Type u} [Field F] [Finite F]
  {W : WeierstrassCurve F}
-- given
  (hF : Nat.card F = 2) :
-- imply
  Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
    (Nat.card F) (Nat.card W.toAffine.Point)) := by
-- proof
  have hle := W.toAffine.natCard_point_le_two_mul_natCard_add_one
  simpa only [hF] using degreeDataAtTwo_of_pointCount_bounds
    (Nat.card W.toAffine.Point) Nat.card_pos (by omega)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

/--
[manin_degree_data_of_card_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
lemma manin_degree_data_of_card_eq_four
  {F : Type u} [Field F] [Finite F]
  {W : WeierstrassCurve F}
-- given
  (hF : Nat.card F = 4) :
-- imply
  Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
    (Nat.card F) (Nat.card W.toAffine.Point)) := by
-- proof
  have hle := W.toAffine.natCard_point_le_two_mul_natCard_add_one
  simpa only [hF] using degreeDataAtFour_of_pointCount_bounds
    (Nat.card W.toAffine.Point) Nat.card_pos (by omega)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[charTwoFiber_card_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma charTwoFiber_card_eq_one [Finite F] [CharP F 2] (c : F) :
  Nat.card (charTwoFiber 0 c) = 1 := by
  have hsquareInjective : Function.Injective (fun y : F ↦ y ^ 2) := by
    intro y z hyz
    obtain hyz | hyz := (sq_eq_sq_iff_eq_or_eq_neg.mp hyz)
    · exact hyz
    · simpa only [CharTwo.neg_eq] using hyz
  obtain ⟨r, hr⟩ := Finite.surjective_of_injective hsquareInjective c
  let _ : Nonempty (charTwoFiber 0 c) := ⟨⟨r, by simpa using hr⟩⟩
  let _ : Subsingleton (charTwoFiber 0 c) := ⟨by
    intro y z
    apply Subtype.ext
    apply hsquareInjective
    simpa using y.property.trans z.property.symm⟩
  exact Nat.card_unique

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[charTwoFiber_card_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma charTwoFiber_card_eq_two [Finite F] [CharP F 2]
  {b c r : F} (hb : b ≠ 0) (hr : r ^ 2 + b * r = c) :
  Nat.card (charTwoFiber b c) = 2 := by
  classical
  have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
  have hrb : (r + b) ^ 2 + b * (r + b) = c := by
    linear_combination hr + (r * b + b ^ 2) * htwo
  have hbr : r + b ≠ r := by
    intro h
    apply hb
    linear_combination h
  let e : charTwoFiber b c ≃ Bool :=
    { toFun := fun y ↦ if y.1 = r then true else false
      invFun := fun value ↦ match value with
        | true => ⟨r, hr⟩
        | false => ⟨r + b, hrb⟩
      left_inv := by
        intro y
        have hfactor : (y.1 + r) * (y.1 + r + b) = 0 := by
          linear_combination y.property + hr + (y.1 * r + c) * htwo
        have hy : y.1 = r ∨ y.1 = r + b := by
          obtain h | h := mul_eq_zero.mp hfactor
          · left
            simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h
          · right
            have hyr : y.1 + r = b := by
              simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h
            calc
              y.1 = (y.1 + r) + r := by
                rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
              _ = b + r := by rw [hyr]
              _ = r + b := add_comm _ _
        apply Subtype.ext
        obtain hy | hy := hy
        · simp [hy]
        · simp [hy, hbr]
      right_inv := by
        intro value
        cases value <;> simp [hbr] }
  simpa using Nat.card_congr e

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[charTwoFiber_card_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma charTwoFiber_card_eq_zero [Finite F] (b c : F)
  (hempty : ¬∃ y, y ^ 2 + b * y = c) :
  Nat.card (charTwoFiber b c) = 0 := by
  let _ : IsEmpty (charTwoFiber b c) := ⟨fun y ↦ hempty ⟨y.1, y.property⟩⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[charTwoFiber_card_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma charTwoFiber_card_le_two [Finite F] [CharP F 2]
  (b c : F) : Nat.card (charTwoFiber b c) ≤ 2 := by
  by_cases hb : b = 0
  · subst b
    rw [charTwoFiber_card_eq_one]
    omega
  by_cases hexists : ∃ y, y ^ 2 + b * y = c
  · obtain ⟨r, hr⟩ := hexists
    rw [charTwoFiber_card_eq_two hb hr]
  · rw [charTwoFiber_card_eq_zero b c hexists]
    omega

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[eval_frobeniusTail](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma eval_frobeniusTail (h k : F[X]) (x : F) (e : ℕ) :
  (frobeniusTail h k e).eval x =
    frobeniusValue (h.eval x) (k.eval x) e := by
  induction e with
  | zero => simp [frobeniusTail, frobeniusValue]
  | succ e ih => simp [frobeniusTail, frobeniusValue, ih]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[frobenius_pow_eq_linear_add_value](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma frobenius_pow_eq_linear_add_value [CharP F 2]
  {b c y : F} (hy : y ^ 2 + b * y = c) (e : ℕ) :
  y ^ (2 ^ e) = b ^ (2 ^ e - 1) * y + frobeniusValue c b e := by
  induction e with
  | zero => simp [frobeniusValue]
  | succ e ih =>
    let q := 2 ^ e
    have hq : 2 ^ (e + 1) = 2 * q := by simp [q, pow_succ, mul_comm]
    have hqpos : 0 < q := by simp [q]
    have hy' : y ^ 2 = b * y + c := by
      calc
        y ^ 2 = c - b * y := eq_sub_of_add_eq hy
        _ = c + b * y := by
          simp only [sub_eq_add_neg, CharTwo.neg_eq]
        _ = b * y + c := add_comm _ _
    have hbpow : (b ^ (q - 1)) ^ 2 = b ^ (2 * q - 2) := by
      rw [← pow_mul]
      congr 1
      omega
    have hbnext : b ^ (2 * q - 2) * (b * y) = b ^ (2 * q - 1) * y := by
      calc
        b ^ (2 * q - 2) * (b * y) =
          (b ^ (2 * q - 2) * b) * y := by ring
        _ = b ^ (2 * q - 2 + 1) * y := by rw [pow_succ]
        _ = b ^ (2 * q - 1) * y := by congr 2; omega
    rw [hq]
    calc
      y ^ (2 * q) = (y ^ q) ^ 2 := by
        rw [← pow_mul]
        congr 1
        omega
      _ = (b ^ (q - 1) * y + frobeniusValue c b e) ^ 2 := by
        rw [show q = 2 ^ e by rfl, ih]
      _ = b ^ (2 * q - 2) * y ^ 2 + frobeniusValue c b e ^ 2 := by
        rw [CharTwo.add_sq, mul_pow, hbpow]
      _ = b ^ (2 * q - 2) * (b * y + c) +
        frobeniusValue c b e ^ 2 := by rw [hy']
      _ = b ^ (2 * q - 1) * y +
        (frobeniusValue c b e ^ 2 + b ^ (2 * q - 2) * c) := by
        rw [mul_add, hbnext]
        ring
      _ = b ^ (2 * q - 1) * y + frobeniusValue c b (e + 1) := by
        rw [frobeniusValue, hq]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[frobenius_polynomial_mod_quadratic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma frobenius_polynomial_mod_quadratic [CharP F 2]
  (b c : F) (e : ℕ) :
  X ^ (2 ^ e) + C (b ^ (2 ^ e - 1)) * X + C (frobeniusValue c b e) =
    charTwoQuadratic b c * frobeniusQuotient b c e := by
  induction e with
  | zero => simp [frobeniusValue, frobeniusQuotient,
    CharTwo.add_self_eq_zero]
  | succ e ih =>
    let q := 2 ^ e
    have hq : 2 ^ (e + 1) = 2 * q := by simp [q, pow_succ, mul_comm]
    have hqpos : 0 < q := by simp [q]
    have hbpow : (b ^ (q - 1)) ^ 2 = b ^ (2 * q - 2) := by
      rw [← pow_mul]
      congr 1
      omega
    have hbnext : b ^ (2 * q - 2) * b = b ^ (2 * q - 1) := by
      calc
        b ^ (2 * q - 2) * b = b ^ (2 * q - 2 + 1) := (pow_succ _ _).symm
        _ = b ^ (2 * q - 1) := by congr 1; omega
    rw [frobeniusValue, frobeniusQuotient, hq]
    rw [show X ^ (2 * q) = (X ^ q) ^ 2 by
      rw [← pow_mul]
      congr 1
      omega]
    rw [show C (b ^ (2 * q - 1)) * X =
      C (b ^ (2 * q - 2)) * (C b * X) by
        calc
          C (b ^ (2 * q - 1)) * X =
            C (b ^ (2 * q - 2) * b) * X := by rw [hbnext]
          _ = (C (b ^ (2 * q - 2)) * C b) * X := by rw [map_mul]
          _ = C (b ^ (2 * q - 2)) * (C b * X) := by ring]
    rw [show C (frobeniusValue c b e ^ 2 + b ^ (2 * q - 2) * c) =
      C (frobeniusValue c b e) ^ 2 +
        C (b ^ (2 * q - 2)) * C c by simp]
    rw [show C (b ^ (2 * q - 2)) = C (b ^ (q - 1)) ^ 2 by
      rw [← map_pow, hbpow]]
    calc
      (X ^ q) ^ 2 + C (b ^ (q - 1)) ^ 2 * (C b * X) +
        (C (frobeniusValue c b e) ^ 2 +
          C (b ^ (q - 1)) ^ 2 * C c) =
        (X ^ q + C (b ^ (q - 1)) * X +
          C (frobeniusValue c b e)) ^ 2 +
            C (b ^ (q - 1)) ^ 2 * charTwoQuadratic b c := by
        rw [CharTwo.add_sq, CharTwo.add_sq]
        unfold charTwoQuadratic
        have htwo : (2 : F[X]) = 0 := CharTwo.two_eq_zero
        linear_combination
          -(X ^ 2 * C (b ^ (q - 1)) ^ 2) * htwo
      _ = (charTwoQuadratic b c * frobeniusQuotient b c e) ^ 2 +
        C (b ^ (q - 1)) ^ 2 * charTwoQuadratic b c := by
        rw [show X ^ q + C (b ^ (q - 1)) * X +
          C (frobeniusValue c b e) =
            charTwoQuadratic b c * frobeniusQuotient b c e by
              simpa only [q] using ih]
      _ = charTwoQuadratic b c *
        (charTwoQuadratic b c * frobeniusQuotient b c e ^ 2 +
          C (b ^ (q - 1)) ^ 2) := by ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[eval_charTwoFrobeniusPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma eval_charTwoFrobeniusPolynomial [Finite F] (x : F) :
  (charTwoFrobeniusPolynomial : F[X]).eval x = 0 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  unfold charTwoFrobeniusPolynomial
  rw [eval_sub, eval_pow, eval_X, @Nat.card_eq_fintype_card F fintypeF,
    FiniteField.pow_card, sub_self]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[charTwoFrobeniusPolynomial_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma charTwoFrobeniusPolynomial_ne_zero [Finite F] :
  (charTwoFrobeniusPolynomial : F[X]) ≠ 0 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hdegree := FiniteField.X_pow_card_sub_X_natDegree_eq F
    (@Fintype.one_lt_card F fintypeF _)
  intro hzero
  unfold charTwoFrobeniusPolynomial at hzero
  rw [@Nat.card_eq_fintype_card F fintypeF] at hzero
  rw [hzero] at hdegree
  simp only [natDegree_zero] at hdegree
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  omega

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[charTwoFrobeniusPolynomial_splits](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma charTwoFrobeniusPolynomial_splits [Finite F] :
  (charTwoFrobeniusPolynomial : F[X]).Splits := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  rw [Polynomial.splits_iff_card_roots]
  unfold charTwoFrobeniusPolynomial
  rw [@Nat.card_eq_fintype_card F fintypeF,
    FiniteField.roots_X_pow_card_sub_X,
    FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]
  simp

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryPoint_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryPoint_add_one [Finite F] [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] (n : ℤ) :
  ordinaryPoint W (n + 1) = ordinaryPoint W n + ordinaryQ W := by
  rw [ordinaryPoint, ordinaryPoint, add_one_zsmul]
  abel

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinary_paper_coordinates_equation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinary_paper_coordinates_equation [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
  {x y : RatFunc F} (hxy : (ordinaryTwist W).toAffine.Nonsingular x y) :
  ordinaryPaperY y ^ 2 + ordinaryPaperX x * ordinaryPaperY y =
    ordinaryPaperX x ^ 3 +
      (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * ordinaryPaperX x ^ 2 +
        RatFunc.C W.a₆ := by
  have heq := hxy.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [ordinaryTwist] at heq
  unfold ordinaryPaperX ordinaryPaperY
  field_simp [RatFunc.X_ne_zero]
  linear_combination heq

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[intDegree_C_div_X_sq_le_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma intDegree_C_div_X_sq_le_zero (b : F) :
  (RatFunc.C b / RatFunc.X ^ 2).intDegree ≤ 0 := by
  by_cases hb : b = 0
  · simp [hb]
  have hCb : RatFunc.C b ≠ 0 := by
    intro hzero
    apply hb
    apply RatFunc.C_injective
    simpa using hzero
  rw [RatFunc.intDegree_div hCb (pow_ne_zero 2 RatFunc.X_ne_zero)]
  rw [intDegree_pow RatFunc.X_ne_zero]
  simp

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinary_coefficient_intDegree_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinary_coefficient_intDegree_le_one (W : WeierstrassCurve F) :
  (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2).intDegree ≤ 1 := by
  exact intDegree_add_le_of_le (m := 1) (by norm_num) (by simp)
    ((intDegree_C_div_X_sq_le_zero W.a₆).trans (by norm_num))

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryPaperY_intDegree_le_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryPaperY_intDegree_le_zero [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
  {x y : RatFunc F} (hxy : (ordinaryTwist W).toAffine.Nonsingular x y)
  (hx : (ordinaryPaperX x).intDegree ≤ 0) :
  (ordinaryPaperY y).intDegree ≤ 0 := by
  let r := ordinaryPaperX x
  let s := ordinaryPaperY y
  by_contra hsnot
  have hspos : 0 < s.intDegree := lt_of_not_ge hsnot
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at hspos
    simp at hspos
  have hs2 : (s ^ 2).intDegree = 2 * s.intDegree := by
    rw [intDegree_pow hs0]
    norm_num
  have hrs : (r * s).intDegree ≤ s.intDegree := by
    simpa using intDegree_mul_le_of_le (x := r) (y := s)
      (m := 0) (n := s.intDegree) (by simpa using hspos.le) hx le_rfl
  have hlhs : (s ^ 2 + r * s).intDegree = 2 * s.intDegree := by
    rw [intDegree_add_eq_left_of_lt (pow_ne_zero 2 hs0), hs2]
    omega
  have hr3 : (r ^ 3).intDegree ≤ 0 := intDegree_pow_le_zero hx 3
  have hr2 : (r ^ 2).intDegree ≤ 0 := intDegree_pow_le_zero hx 2
  have hmiddle :
    ((RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2).intDegree ≤ 1 :=
    intDegree_mul_le_of_le (m := 1) (n := 0) (by norm_num)
      (ordinary_coefficient_intDegree_le_one W) hr2
  have hrhs :
    (r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
      RatFunc.C W.a₆).intDegree ≤ 1 := by
    have hfirst := intDegree_add_le_of_le (m := 1) (by norm_num)
      (hr3.trans (by norm_num)) hmiddle
    exact intDegree_add_le_of_le (m := 1) (by norm_num) hfirst (by simp)
  have heq := ordinary_paper_coordinates_equation W hxy
  change s ^ 2 + r * s =
    r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
      RatFunc.C W.a₆ at heq
  have hlhsLe : (s ^ 2 + r * s).intDegree ≤ 1 := by rw [heq]; exact hrhs
  rw [hlhs] at hlhsLe
  omega

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryPaperX_addX_Q_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryPaperX_addX_Q_eq [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
  {x y : RatFunc F} (hx : x ≠ RatFunc.X ^ 3) :
  ordinaryPaperX
    ((ordinaryTwist W).toAffine.addX x (RatFunc.X ^ 3)
      ((ordinaryTwist W).toAffine.slope x (RatFunc.X ^ 3) y 0)) =
    (ordinaryPaperY y /
      (ordinaryPaperX x - RatFunc.X)) ^ 2 +
      ordinaryPaperY y / (ordinaryPaperX x - RatFunc.X) +
        RatFunc.C W.a₆ / RatFunc.X ^ 2 + ordinaryPaperX x := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addX, ordinaryTwist, sub_zero]
  unfold ordinaryPaperX ordinaryPaperY
  field_simp [RatFunc.X_ne_zero, hx]
  have htwo : (2 : RatFunc F) = 0 := CharTwo.two_eq_zero
  simp only [sub_eq_add_neg, CharTwo.neg_eq]
  linear_combination RatFunc.X ^ 3 * (x + RatFunc.X ^ 3) ^ 2 * htwo

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryPaperX_addX_Q_intDegree_le_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryPaperX_addX_Q_intDegree_le_zero [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
  {x y : RatFunc F} (hxy : (ordinaryTwist W).toAffine.Nonsingular x y)
  (hxQ : x ≠ RatFunc.X ^ 3)
  (hx : (ordinaryPaperX x).intDegree ≤ 0) :
  (ordinaryPaperX
    ((ordinaryTwist W).toAffine.addX x (RatFunc.X ^ 3)
      ((ordinaryTwist W).toAffine.slope x (RatFunc.X ^ 3) y 0))).intDegree ≤ 0 := by
  let r := ordinaryPaperX x
  let s := ordinaryPaperY y
  change r.intDegree ≤ 0 at hx
  have hs : s.intDegree ≤ 0 := ordinaryPaperY_intDegree_le_zero W hxy hx
  have hdiff : r - RatFunc.X ≠ 0 := by
    intro hzero
    have hr : r = RatFunc.X := sub_eq_zero.mp hzero
    apply hxQ
    unfold r ordinaryPaperX at hr
    calc
      x = RatFunc.X * RatFunc.X ^ 2 :=
        (div_eq_iff (pow_ne_zero 2 RatFunc.X_ne_zero)).mp hr
      _ = RatFunc.X ^ 3 := by ring
  have hdiffDegree : (r - RatFunc.X).intDegree = 1 := by
    rw [show r - RatFunc.X = -RatFunc.X + r by ring]
    rw [intDegree_add_eq_left_of_lt (neg_ne_zero.mpr RatFunc.X_ne_zero)]
    · simp
    · rw [RatFunc.intDegree_neg]
      norm_num
      omega
  have hslope : (s / (r - RatFunc.X)).intDegree ≤ 0 := by
    by_cases hs0 : s = 0
    · simp [hs0]
    rw [RatFunc.intDegree_div hs0 hdiff, hdiffDegree]
    omega
  have hslope2 : ((s / (r - RatFunc.X)) ^ 2).intDegree ≤ 0 :=
    intDegree_pow_le_zero hslope 2
  rw [ordinaryPaperX_addX_Q_eq W hxQ]
  change ((s / (r - RatFunc.X)) ^ 2 + s / (r - RatFunc.X) +
    RatFunc.C W.a₆ / RatFunc.X ^ 2 + r).intDegree ≤ 0
  have hfirst := intDegree_add_le_of_le (m := 0) (by norm_num) hslope2 hslope
  have hsecond := intDegree_add_le_of_le (m := 0) (by norm_num) hfirst
    (intDegree_C_div_X_sq_le_zero W.a₆)
  exact intDegree_add_le_of_le (m := 0) (by norm_num) hsecond hx

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryPaperX_Q_coordinate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryPaperX_Q_coordinate :
  ordinaryPaperX (RatFunc.X ^ 3 : RatFunc F) = RatFunc.X := by
  unfold ordinaryPaperX
  field_simp [RatFunc.X_ne_zero]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryBadAtInfinity_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryBadAtInfinity_neg [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
  (P : (ordinaryTwist W).toAffine.Point) :
  ordinaryBadAtInfinity W (-P) ↔ ordinaryBadAtInfinity W P := by
  cases P with
  | zero => rfl
  | some x y hxy =>
    rw [WeierstrassCurve.Affine.Point.neg_some]
    rfl

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryBadAtInfinity_add_Q](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryBadAtInfinity_add_Q [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
  {P : (ordinaryTwist W).toAffine.Point}
  (hP : ordinaryBadAtInfinity W P) :
  ordinaryBadAtInfinity W (P + ordinaryQ W) := by
  cases P with
  | zero => simp [ordinaryBadAtInfinity] at hP
  | some x y hxy =>
    change (ordinaryPaperX x).intDegree ≤ 0 at hP
    have hx : x ≠ RatFunc.X ^ 3 := by
      intro hx
      have hpaper : ordinaryPaperX x = RatFunc.X := by
        rw [hx, ordinaryPaperX_Q_coordinate]
      rw [hpaper] at hP
      norm_num at hP
    have hvertical :
      ¬(x = RatFunc.X ^ 3 ∧
        y = (ordinaryTwist W).toAffine.negY (RatFunc.X ^ 3) 0) :=
      fun h ↦ hx h.1
    rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 _ from rfl]
    rw [WeierstrassCurve.Affine.Point.add_some hvertical]
    exact ordinaryPaperX_addX_Q_intDegree_le_zero W hxy hx hP

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryBadAtInfinity_sub_Q](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryBadAtInfinity_sub_Q [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
  {P : (ordinaryTwist W).toAffine.Point}
  (hP : ordinaryBadAtInfinity W P) :
  ordinaryBadAtInfinity W (P - ordinaryQ W) := by
  have hnegP : ordinaryBadAtInfinity W (-P) :=
    (ordinaryBadAtInfinity_neg W P).mpr hP
  have hadd := ordinaryBadAtInfinity_add_Q W hnegP
  rw [show P - ordinaryQ W = -(-P + ordinaryQ W) by abel]
  exact (ordinaryBadAtInfinity_neg W (-P + ordinaryQ W)).mpr hadd

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryBadAtInfinity_add_Q_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryBadAtInfinity_add_Q_iff [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
  (P : (ordinaryTwist W).toAffine.Point) :
  ordinaryBadAtInfinity W (P + ordinaryQ W) ↔ ordinaryBadAtInfinity W P := by
  refine ⟨fun h ↦ ?_, ordinaryBadAtInfinity_add_Q W⟩
  have hsub := ordinaryBadAtInfinity_sub_Q W h
  simpa using hsub

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryPaperX_pZeroX](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryPaperX_pZeroX [Finite F] :
  ordinaryPaperX (ordinaryPZeroX (F := F)) = RatFunc.X ^ Nat.card F := by
  unfold ordinaryPaperX ordinaryPZeroX
  rw [show Nat.card F + 2 = 2 + Nat.card F by omega, pow_add]
  field_simp [RatFunc.X_ne_zero]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryPZero_not_badAtInfinity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryPZero_not_badAtInfinity [Finite F] [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
  ¬ordinaryBadAtInfinity W (ordinaryPZero W) := by
  intro hbad
  change (ordinaryPaperX (ordinaryPZeroX (F := F))).intDegree ≤ 0 at hbad
  rw [ordinaryPaperX_pZeroX, intDegree_pow RatFunc.X_ne_zero] at hbad
  simp only [RatFunc.intDegree_X, mul_one] at hbad
  have hcard : (0 : ℤ) < Nat.card F := by exact_mod_cast Nat.card_pos
  omega

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryPoint_not_badAtInfinity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryPoint_not_badAtInfinity [Finite F] [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] (n : ℤ) :
  ¬ordinaryBadAtInfinity W (ordinaryPoint W n) := by
  refine Int.inductionOn' n 0 ?_ ?_ ?_
  · simpa [ordinaryPoint] using ordinaryPZero_not_badAtInfinity W
  · intro k _ hk hbad
    apply hk
    apply (ordinaryBadAtInfinity_add_Q_iff W (ordinaryPoint W k)).mp
    rwa [← ordinaryPoint_add_one W k]
  · intro k _ hk hbad
    apply hk
    have hstep := ordinaryPoint_add_one W (k - 1)
    rw [show k - 1 + 1 = k by ring] at hstep
    rw [hstep]
    exact (ordinaryBadAtInfinity_add_Q_iff W (ordinaryPoint W (k - 1))).mpr hbad

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryQ_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryQ_ne_zero [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
  ordinaryQ W ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero _

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryD_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryD_zero [Finite F] [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
  ordinaryD W 0 = Nat.card F := by
  rw [ordinaryD, ordinaryPoint]
  simp only [zero_zsmul, add_zero, ordinaryPZero,
    WeierstrassCurve.Affine.Point.mk]
  have hx : ordinaryPaperX (ordinaryPZeroX (F := F)) =
    RatFunc.X ^ Nat.card F := by
    unfold ordinaryPaperX ordinaryPZeroX
    rw [show Nat.card F + 2 = 2 + Nat.card F by omega, pow_add]
    field_simp [RatFunc.X_ne_zero]
  rw [hx]
  change (RatFunc.num ((algebraMap F[X] (RatFunc F) X) ^ Nat.card F)).natDegree =
    Nat.card F
  rw [← map_pow, RatFunc.num_algebraMap, Polynomial.natDegree_X_pow]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinary_num_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinary_num_degree [Finite F] [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
  {n : ℤ} {x y : RatFunc F}
  {hxy : (ordinaryTwist W).toAffine.Nonsingular x y}
  (hn : ordinaryPoint W n = .some x y hxy) :
  (RatFunc.denom (ordinaryPaperX x)).natDegree <
    (RatFunc.num (ordinaryPaperX x)).natDegree := by
  have hnotBad := ordinaryPoint_not_badAtInfinity W n
  have hnotLe : ¬(ordinaryPaperX x).intDegree ≤ 0 := by
    intro hdegree
    apply hnotBad
    rwa [hn]
  have hpos : 0 < (ordinaryPaperX x).intDegree := lt_of_not_ge hnotLe
  unfold RatFunc.intDegree at hpos
  omega

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryD_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryD_eq_zero_iff [Finite F] [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
  (n : ℤ) :
  ordinaryD W n = 0 ↔ ordinaryPoint W n = 0 := by
  cases hp : ordinaryPoint W n with
  | zero =>
    constructor
    · exact fun _ ↦ WeierstrassCurve.Affine.Point.zero_def.symm
    · intro _
      simp [ordinaryD, hp]
  | some x y hxy =>
    have hdeg := ordinary_num_degree W hp
    constructor
    · intro hd
      simp only [ordinaryD, hp] at hd
      omega
    · exact fun hpzero ↦ (WeierstrassCurve.Affine.Point.some_ne_zero hxy hpzero).elim

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryNoAdjacentZeros](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryNoAdjacentZeros [Finite F] [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
  : ∀ n, ordinaryD W n = 0 → ordinaryD W (n + 1) = 0 → False := by
  intro n hn hn1
  have hp := (ordinaryD_eq_zero_iff W n).mp hn
  have hp1 := (ordinaryD_eq_zero_iff W (n + 1)).mp hn1
  apply ordinaryQ_ne_zero W
  have hs := ordinaryPoint_add_one W n
  rw [hp, hp1] at hs
  simpa using hs.symm

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryH_derivative](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryH_derivative [CharP F 2] (W : WeierstrassCurve F) :
  (ordinaryH W).derivative = X ^ 2 := by
  unfold ordinaryH
  simp only [derivative_add, derivative_mul, derivative_pow, derivative_X,
    derivative_C]
  have htwo : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
  have hthree : ((3 : ℕ) : F) = 1 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, Nat.cast_add, htwo,
      Nat.cast_one, zero_add]
  rw [htwo, hthree, map_zero, map_one]
  norm_num

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[derivative_frobeniusTail_ordinary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma derivative_frobeniusTail_ordinary [CharP F 2]
  (W : WeierstrassCurve F) (e : ℕ) (he : 0 < e) :
  (frobeniusTail (ordinaryH W) X e).derivative = X ^ (2 ^ e) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
  rw [frobeniusTail]
  have hexponent : 2 ^ (e + 1) - 2 = 2 * (2 ^ e - 1) := by
    rw [pow_succ]
    omega
  rw [hexponent, show X ^ (2 * (2 ^ e - 1)) =
    (X ^ (2 ^ e - 1)) ^ 2 by
      rw [← pow_mul]
      congr 1
      omega]
  rw [derivative_add, derivative_pow, derivative_mul, derivative_pow,
    ordinaryH_derivative]
  have htwo : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
  rw [htwo, map_zero]
  norm_num
  rw [← pow_mul, ← pow_add]
  congr 1
  rw [pow_succ]
  have hpowpos : 0 < 2 ^ e := pow_pos (by norm_num) e
  omega

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryH_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryH_natDegree (W : WeierstrassCurve F) :
  (ordinaryH W).natDegree = 3 := by
  unfold ordinaryH
  compute_degree <;> norm_num

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[frobeniusTail_ordinary_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma frobeniusTail_ordinary_natDegree
  (W : WeierstrassCurve F) (e : ℕ) (he : 0 < e) :
  (frobeniusTail (ordinaryH W) X e).natDegree = 3 * 2 ^ (e - 1) := by
  induction e using Nat.twoStepInduction with
  | zero => omega
  | one => simp [frobeniusTail, ordinaryH_natDegree]
  | more e ih ih1 =>
    rw [frobeniusTail]
    have htail : frobeniusTail (ordinaryH W) X (e + 1) ≠ 0 := by
      intro hzero
      have hdegree := ih1 (by omega)
      rw [hzero] at hdegree
      simp at hdegree
    have hxpow : X ^ (2 ^ (e + 2) - 2) ≠ (0 : F[X]) :=
      pow_ne_zero _ X_ne_zero
    have hH : ordinaryH W ≠ 0 := by
      intro hzero
      have hdegree := ordinaryH_natDegree W
      rw [hzero] at hdegree
      simp at hdegree
    rw [natDegree_add_eq_left_of_natDegree_lt]
    · rw [natDegree_pow, ih1 (by omega)]
      simp [pow_succ]
      ring
    · rw [natDegree_mul hxpow hH, natDegree_pow, natDegree_X,
      ordinaryH_natDegree, natDegree_pow, ih1 (by omega)]
      norm_num
      have hpow : 2 ≤ 2 ^ (e + 1) := by
        rw [pow_succ]
        have hpos : 0 < 2 ^ e := pow_pos (by norm_num) e
        omega
      rw [pow_succ]
      omega

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[eval_ordinaryU](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma eval_ordinaryU [Finite F] (W : WeierstrassCurve F) (x : F) :
  (ordinaryU W).eval x =
    x * frobeniusValue ((ordinaryH W).eval x) x
      (charTwoExponent (F := F)) := by
  simp only [ordinaryU, eval_mul, eval_X, eval_frobeniusTail]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[eval_ordinaryMinusOneNumerator](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma eval_ordinaryMinusOneNumerator [Finite F] [CharP F 2]
  (W : WeierstrassCurve F) (x : F) :
  (ordinaryMinusOneNumerator W).eval x =
    x ^ 2 + x * frobeniusValue ((ordinaryH W).eval x) x
      (charTwoExponent (F := F)) := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hxq : x ^ Nat.card F = x := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card x
  have hx2q1 : x ^ (2 * Nat.card F + 1) = x ^ 3 := by
    calc
      x ^ (2 * Nat.card F + 1) = x ^ (2 * Nat.card F) * x := pow_succ _ _
      _ = (x ^ Nat.card F) ^ 2 * x := by
        rw [show 2 * Nat.card F = Nat.card F * 2 by omega, pow_mul]
      _ = x ^ 3 := by rw [hxq]; ring
  have hxq2 : x ^ (Nat.card F + 2) = x ^ 3 := by
    rw [pow_add, hxq]
    ring
  have hxq1 : x ^ (Nat.card F + 1) = x ^ 2 := by
    rw [pow_add, hxq]
    ring
  simp only [ordinaryMinusOneNumerator, eval_add, eval_pow, eval_X,
    eval_ordinaryU, hx2q1, hxq2, hxq1]
  have hcancel : x ^ 3 + x ^ 3 = 0 := CharTwo.add_self_eq_zero _
  linear_combination hcancel

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[frobeniusValue_zero_coefficient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma frobeniusValue_zero_coefficient (c : F) (e : ℕ) (he : 0 < e) :
  frobeniusValue c 0 e = c ^ (2 ^ (e - 1)) := by
  induction e using Nat.twoStepInduction with
  | zero => omega
  | one => simp [frobeniusValue]
  | more e ih ih1 =>
    rw [frobeniusValue, ih1 (by omega)]
    have hexponent : 0 < 2 ^ (e + 2) - 2 := by
      have hpowpos : 0 < 2 ^ e := pow_pos (by norm_num) e
      rw [show e + 2 = (e + 1) + 1 by omega, pow_succ, pow_succ]
      omega
    rw [zero_pow (Nat.ne_of_gt hexponent), zero_mul, add_zero, ← pow_mul]
    congr 1

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryPointCount_eq_fiber_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryPointCount_eq_fiber_sum [Fintype F] [CharP F 2]
  (W : WeierstrassCurve F) [W.IsCharTwoJNeZeroNF] [W.IsElliptic] :
  Nat.card W.toAffine.Point =
    (∑ x : F, Nat.card (charTwoFiber x ((ordinaryH W).eval x))) + 1 := by
  rw [W.toAffine.natCard_point_eq_natCard_affineSolutions_add_one]
  rw [Nat.card_congr (affineSolutionsEquivOrdinaryFibers W), Nat.card_sigma]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[rootMultiplicity_ordinaryNumerator_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma rootMultiplicity_ordinaryNumerator_eq_zero [Finite F]
  [CharP F 2] (W : WeierstrassCurve F) (x : F) (hx : x ≠ 0)
  (hvalue : frobeniusValue ((ordinaryH W).eval x) x
    (charTwoExponent (F := F)) = 0) :
  Polynomial.rootMultiplicity x (ordinaryMinusOneNumerator W) = 0 := by
  apply Polynomial.rootMultiplicity_eq_zero
  intro hroot
  have heval := eval_ordinaryMinusOneNumerator W x
  rw [hvalue, mul_zero, add_zero] at heval
  exact (pow_ne_zero 2 hx) (heval.symm.trans hroot)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[count_roots_charTwoFrobeniusPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma count_roots_charTwoFrobeniusPolynomial [Finite F] (x : F) :
  Multiset.count x (charTwoFrobeniusPolynomial : F[X]).roots = 1 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  unfold charTwoFrobeniusPolynomial
  rw [@Nat.card_eq_fintype_card F fintypeF,
    FiniteField.roots_X_pow_card_sub_X]
  simp

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[count_roots_charTwoFrobeniusPolynomial_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma count_roots_charTwoFrobeniusPolynomial_sq [Finite F] (x : F) :
  Multiset.count x ((charTwoFrobeniusPolynomial : F[X]) ^ 2).roots = 2 := by
  rw [Polynomial.roots_pow, Multiset.count_nsmul,
    count_roots_charTwoFrobeniusPolynomial]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[charTwo_natDegree_num_div](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma charTwo_natDegree_num_div (p q : F[X]) (hq : q ≠ 0) :
  (RatFunc.num
    (algebraMap F[X] (RatFunc F) p /
      algebraMap F[X] (RatFunc F) q)).natDegree =
    (p / gcd p q).natDegree := by
  have hg : gcd p q ≠ 0 := by
    intro hzero
    exact hq ((gcd_eq_zero_iff _ _).mp hzero).2
  have hgdivq : gcd p q ∣ q := gcd_dvd_right _ _
  have hmul : gcd p q * (q / gcd p q) = q :=
    EuclideanDomain.mul_div_cancel' hg hgdivq
  have hquotient : q / gcd p q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact hq hmul.symm
  rw [RatFunc.num_div, Polynomial.natDegree_C_mul]
  exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hquotient)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryPZeroX_ne_QX](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryPZeroX_ne_QX [Finite F] :
  ordinaryPZeroX (F := F) ≠ RatFunc.X ^ 3 := by
  intro heq
  have hdegree := congrArg RatFunc.intDegree heq
  simp only [ordinaryPZeroX] at hdegree
  rw [intDegree_pow RatFunc.X_ne_zero,
    intDegree_pow RatFunc.X_ne_zero] at hdegree
  simp only [RatFunc.intDegree_X, mul_one] at hdegree
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  omega

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryPaperY_neg_pZeroY](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryPaperY_neg_pZeroY [Finite F] [CharP F 2]
  (W : WeierstrassCurve F) :
  ordinaryPaperY
    ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
      (ordinaryPZeroY W)) =
    algebraMap F[X] (RatFunc F) (ordinaryU W) / RatFunc.X +
      RatFunc.X ^ Nat.card F := by
  simp only [WeierstrassCurve.Affine.negY, ordinaryTwist,
    ordinaryPZeroX, ordinaryPZeroY, sub_eq_add_neg, CharTwo.neg_eq]
  unfold ordinaryPaperY
  rw [map_mul, map_pow, RatFunc.algebraMap_X]
  field_simp [RatFunc.X_ne_zero]
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[algebraMap_charTwoFrobeniusPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma algebraMap_charTwoFrobeniusPolynomial [Finite F] [CharP F 2] :
  algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial =
    RatFunc.X ^ Nat.card F + RatFunc.X := by
  simp only [charTwoFrobeniusPolynomial, sub_eq_add_neg, CharTwo.neg_eq,
    map_add, map_pow, RatFunc.algebraMap_X]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinary_product_formula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinary_product_formula {R : Type*} [CommRing R] [CharP R 2]
  (t f g b z : R)
  (curve : z ^ 2 + t * f * g * z + t ^ 2 * f ^ 3 * g +
    b * t ^ 2 * g ^ 4 + t ^ 3 * f ^ 2 * g ^ 2 + b * f ^ 2 * g ^ 2 = 0) :
  (t * f * (t * g + f) + t * f * g + z) *
    (t * f * (t * g + f) + z) =
    (t ^ 2 * f ^ 2 + b * g ^ 2) * (t * g + f) ^ 2 := by
  have htwo : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination curve +
    (-t * f * g ^ 3 * b + t * f ^ 2 * z + t ^ 2 * f * g * z -
      t ^ 2 * g ^ 4 * b - f ^ 2 * g ^ 2 * b) * htwo

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryNeighborFirst_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryNeighborFirst_natDegree
  (W : WeierstrassCurve F) {f g : F[X]} (hf : f ≠ 0)
  (hdegree : g.natDegree < f.natDegree) :
  (ordinaryNeighborFirst W f g).natDegree = 2 * f.natDegree + 2 := by
  have hXf : (X * f).natDegree = f.natDegree + 1 := by
    rw [Polynomial.natDegree_mul X_ne_zero hf, Polynomial.natDegree_X]
    omega
  have hmain : ((X * f) ^ 2).natDegree = 2 * f.natDegree + 2 := by
    rw [Polynomial.natDegree_pow, hXf]
    omega
  have hremainder : (C W.a₆ * g ^ 2).natDegree < 2 * f.natDegree + 2 := by
    calc
      (C W.a₆ * g ^ 2).natDegree ≤ (g ^ 2).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ = 2 * g.natDegree := Polynomial.natDegree_pow _ _
      _ < 2 * f.natDegree + 2 := by omega
  unfold ordinaryNeighborFirst
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact hmain
  · rwa [hmain]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryNeighbor_primitive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryNeighbor_primitive [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
  {f g : F[X]} (hfg : IsCoprime f g) (hden : X * g + f ≠ 0) :
  PrimitiveTriple (ordinaryNeighborFirst W f g)
    (ordinaryNeighborSecond f g) (neighborDenominator f g) := by
  have hb : W.a₆ ≠ 0 := by
    have h := W.Δ'.ne_zero
    rwa [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
  apply primitiveTriple_of_no_common_irreducible
    (pow_ne_zero 2 hden)
  intro p hp hpFirst hpSecond hpDen
  have hprime := hp.prime
  have hpD : p ∣ X * g + f := hprime.dvd_of_dvd_pow hpDen
  have forceG (hpMain : p ∣ (X * f) ^ 2) : p ∣ g := by
    have hpRest : p ∣ C W.a₆ * g ^ 2 := by
      have hdifference := hpFirst.sub hpMain
      convert hdifference using 1
      unfold ordinaryNeighborFirst
      ring
    obtain hpC | hpg := hprime.dvd_mul.mp hpRest
    · have hCunit : IsUnit (C W.a₆) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb)
      exact (hprime.not_dvd_one
        (hpC.trans (isUnit_iff_dvd_one.mp hCunit))).elim
    · exact hprime.dvd_of_dvd_pow hpg
  have commonDvd (hpf : p ∣ f) (hpg : p ∣ g) : False :=
    hp.not_isUnit (hfg.isUnit_of_dvd' hpf hpg)
  obtain hpXf | hpg := hprime.dvd_mul.mp hpSecond
  · rcases hprime.dvd_mul.mp hpXf with hpX | hpf
    · have hpMain : p ∣ (X * f) ^ 2 := by
      simpa [pow_two] using (hpX.mul_right f).mul_right (X * f)
      have hpg := forceG hpMain
      have hpf : p ∣ f := by
        have hdifference := hpD.sub (hpX.mul_right g)
        convert hdifference using 1
        ring
      exact commonDvd hpf hpg
    · have hpMain : p ∣ (X * f) ^ 2 := by
      simpa [pow_two] using hpXf.mul_right (X * f)
      exact commonDvd hpf (forceG hpMain)
  · have hpf : p ∣ f := by
    have hdifference := hpD.sub (hpg.mul_left X)
    convert hdifference using 1
    ring
    exact commonDvd hpf hpg

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryNeighborFirst_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryNeighborFirst_ratio (W : WeierstrassCurve F)
  (r : RatFunc F) :
  algebraMap F[X] (RatFunc F) (ordinaryNeighborFirst W r.num r.denom) /
    algebraMap F[X] (RatFunc F) (neighborDenominator r.num r.denom) =
    (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C W.a₆) /
      (RatFunc.X + r) ^ 2 := by
  simp only [ordinaryNeighborFirst, neighborDenominator, map_add, map_mul,
    map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  let d := algebraMap F[X] (RatFunc F) r.denom
  have hd : d ≠ 0 := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum : algebraMap F[X] (RatFunc F) r.num = r * d := by
    exact (div_eq_iff hd).mp (RatFunc.num_div_denom r)
  change
    ((RatFunc.X * algebraMap F[X] (RatFunc F) r.num) ^ 2 +
      RatFunc.C W.a₆ * d ^ 2) /
      (RatFunc.X * d + algebraMap F[X] (RatFunc F) r.num) ^ 2 = _
  rw [hnum]
  rw [show (RatFunc.X * (r * d)) ^ 2 + RatFunc.C W.a₆ * d ^ 2 =
    d ^ 2 * (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C W.a₆) by ring]
  rw [show (RatFunc.X * d + r * d) ^ 2 =
    d ^ 2 * (RatFunc.X + r) ^ 2 by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hd)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryNeighborSecond_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryNeighborSecond_ratio (r : RatFunc F) :
  algebraMap F[X] (RatFunc F) (ordinaryNeighborSecond r.num r.denom) /
    algebraMap F[X] (RatFunc F) (neighborDenominator r.num r.denom) =
    RatFunc.X * r / (RatFunc.X + r) ^ 2 := by
  simp only [ordinaryNeighborSecond, neighborDenominator, map_add, map_mul,
    map_pow, RatFunc.algebraMap_X]
  let d := algebraMap F[X] (RatFunc F) r.denom
  have hd : d ≠ 0 := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum : algebraMap F[X] (RatFunc F) r.num = r * d := by
    exact (div_eq_iff hd).mp (RatFunc.num_div_denom r)
  change
    RatFunc.X * algebraMap F[X] (RatFunc F) r.num * d /
      (RatFunc.X * d + algebraMap F[X] (RatFunc F) r.num) ^ 2 = _
  rw [hnum]
  rw [show RatFunc.X * (r * d) * d = d ^ 2 * (RatFunc.X * r) by ring]
  rw [show (RatFunc.X * d + r * d) ^ 2 =
    d ^ 2 * (RatFunc.X + r) ^ 2 by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hd)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinary_neighbor_plus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinary_neighbor_plus [CharP F 2]
  (W : WeierstrassCurve F) {r s : RatFunc F}
  (heq : s ^ 2 + r * s =
    r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
      RatFunc.C W.a₆)
  (hdiff : RatFunc.X + r ≠ 0) :
  (s / (r - RatFunc.X)) ^ 2 + s / (r - RatFunc.X) +
    RatFunc.C W.a₆ / RatFunc.X ^ 2 + r =
    (RatFunc.X * r * (RatFunc.X + r) + RatFunc.X * s) /
      (RatFunc.X + r) ^ 2 := by
  have hdiffEq : r - RatFunc.X = RatFunc.X + r := by
    simp only [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  have hs2 : s ^ 2 =
    r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
      RatFunc.C W.a₆ + r * s := by
    calc
      s ^ 2 = (s ^ 2 + r * s) + r * s := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = _ := by rw [heq]
  rw [div_pow, hs2, hdiffEq]
  field_simp [hdiff, RatFunc.X_ne_zero]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, zero_add, add_zero]
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinary_neighbor_minus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinary_neighbor_minus [CharP F 2]
  (W : WeierstrassCurve F) {r s : RatFunc F}
  (heq : s ^ 2 + r * s =
    r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
      RatFunc.C W.a₆)
  (hdiff : RatFunc.X + r ≠ 0) :
  ((s + r) / (r - RatFunc.X)) ^ 2 +
    (s + r) / (r - RatFunc.X) +
      RatFunc.C W.a₆ / RatFunc.X ^ 2 + r =
    (RatFunc.X * r * (RatFunc.X + r) + RatFunc.X * r + RatFunc.X * s) /
      (RatFunc.X + r) ^ 2 := by
  have hdiffEq : r - RatFunc.X = RatFunc.X + r := by
    simp only [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  have hs2 : s ^ 2 =
    r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
      RatFunc.C W.a₆ + r * s := by
    calc
      s ^ 2 = (s ^ 2 + r * s) + r * s := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = _ := by rw [heq]
  have hsr2 : (s + r) ^ 2 =
    r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
      RatFunc.C W.a₆ + r * s + r ^ 2 := by
    calc
      (s + r) ^ 2 = s ^ 2 + r ^ 2 := by
        rw [add_sq, show (2 : RatFunc F) = 0 from CharTwo.two_eq_zero]
        ring
      _ = _ := by rw [hs2]
  rw [div_pow, hsr2, hdiffEq]
  field_simp [hdiff, RatFunc.X_ne_zero]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, zero_add, add_zero]
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinary_neighbor_pair_product](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinary_neighbor_pair_product [CharP F 2]
  (W : WeierstrassCurve F) {r s : RatFunc F}
  (heq : s ^ 2 + r * s =
    r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
      RatFunc.C W.a₆)
  (hdiff : RatFunc.X + r ≠ 0) :
  ((s / (r - RatFunc.X)) ^ 2 + s / (r - RatFunc.X) +
    RatFunc.C W.a₆ / RatFunc.X ^ 2 + r) *
    (((s + r) / (r - RatFunc.X)) ^ 2 +
      (s + r) / (r - RatFunc.X) +
        RatFunc.C W.a₆ / RatFunc.X ^ 2 + r) =
    (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C W.a₆) /
      (RatFunc.X + r) ^ 2 := by
  rw [ordinary_neighbor_plus W heq hdiff,
    ordinary_neighbor_minus W heq hdiff]
  have heq' := heq
  field_simp [RatFunc.X_ne_zero] at heq'
  have heq'' :
    s * r * RatFunc.X ^ 2 + s ^ 2 * RatFunc.X ^ 2 =
      r ^ 2 * RatFunc.X ^ 3 + r ^ 2 * RatFunc.C W.a₆ +
        r ^ 3 * RatFunc.X ^ 2 + RatFunc.X ^ 2 * RatFunc.C W.a₆ := by
    calc
      _ = s * (s + r) * RatFunc.X ^ 2 := by ring
      _ = r ^ 2 *
        (r * RatFunc.X ^ 2 + (RatFunc.X ^ 3 + RatFunc.C W.a₆)) +
          RatFunc.X ^ 2 * RatFunc.C W.a₆ := heq'
      _ = _ := by ring
  have hcurve :
    (RatFunc.X * s) ^ 2 + RatFunc.X * r * (RatFunc.X * s) +
      RatFunc.X ^ 2 * r ^ 3 + RatFunc.C W.a₆ * RatFunc.X ^ 2 +
        RatFunc.X ^ 3 * r ^ 2 + RatFunc.C W.a₆ * r ^ 2 = 0 := by
    calc
      _ = (s * r * RatFunc.X ^ 2 + s ^ 2 * RatFunc.X ^ 2) +
        (r ^ 2 * RatFunc.X ^ 3 + r ^ 2 * RatFunc.C W.a₆ +
          r ^ 3 * RatFunc.X ^ 2 + RatFunc.X ^ 2 * RatFunc.C W.a₆) := by
          ring
      _ = (r ^ 2 * RatFunc.X ^ 3 + r ^ 2 * RatFunc.C W.a₆ +
        r ^ 3 * RatFunc.X ^ 2 + RatFunc.X ^ 2 * RatFunc.C W.a₆) +
        (r ^ 2 * RatFunc.X ^ 3 + r ^ 2 * RatFunc.C W.a₆ +
          r ^ 3 * RatFunc.X ^ 2 + RatFunc.X ^ 2 * RatFunc.C W.a₆) := by
            rw [heq'']
      _ = 0 := CharTwo.add_self_eq_zero _
  have hcurve' :
    (RatFunc.X * s) ^ 2 + RatFunc.X * r * 1 * (RatFunc.X * s) +
      RatFunc.X ^ 2 * r ^ 3 * 1 +
        RatFunc.C W.a₆ * RatFunc.X ^ 2 * 1 ^ 4 +
          RatFunc.X ^ 3 * r ^ 2 * 1 ^ 2 +
            RatFunc.C W.a₆ * r ^ 2 * 1 ^ 2 = 0 := by
    simpa using hcurve
  have hformula := ordinary_product_formula RatFunc.X r 1
    (RatFunc.C W.a₆) (RatFunc.X * s) hcurve'
  field_simp [hdiff]
  linear_combination hformula

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinary_neighbor_pair_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinary_neighbor_pair_sum [CharP F 2]
  (W : WeierstrassCurve F) {r s : RatFunc F}
  (hdiff : RatFunc.X + r ≠ 0) :
  ((s / (r - RatFunc.X)) ^ 2 + s / (r - RatFunc.X) +
    RatFunc.C W.a₆ / RatFunc.X ^ 2 + r) +
    (((s + r) / (r - RatFunc.X)) ^ 2 +
      (s + r) / (r - RatFunc.X) +
        RatFunc.C W.a₆ / RatFunc.X ^ 2 + r) =
    RatFunc.X * r / (RatFunc.X + r) ^ 2 := by
  have hdiff' : r - RatFunc.X ≠ 0 := by
    simpa only [sub_eq_add_neg, CharTwo.neg_eq, add_comm] using hdiff
  field_simp [hdiff, hdiff', RatFunc.X_ne_zero]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, CharTwo.neg_eq, sub_eq_add_neg, mul_zero, zero_add, add_zero]
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryPaperY_negY](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryPaperY_negY [CharP F 2]
  (W : WeierstrassCurve F) (x y : RatFunc F) :
  ordinaryPaperY ((ordinaryTwist W).toAffine.negY x y) =
    ordinaryPaperY y + ordinaryPaperX x := by
  simp only [WeierstrassCurve.Affine.negY, ordinaryTwist,
    sub_eq_add_neg, CharTwo.neg_eq]
  unfold ordinaryPaperY ordinaryPaperX
  field_simp [RatFunc.X_ne_zero]
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[neighborPolynomial_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma neighborPolynomial_ne_zero (r : RatFunc F)
  (hdiff : RatFunc.X + r ≠ 0) : X * r.denom + r.num ≠ 0 := by
  intro hzero
  have hden : algebraMap F[X] (RatFunc F) r.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum : algebraMap F[X] (RatFunc F) r.num =
    r * algebraMap F[X] (RatFunc F) r.denom :=
    (div_eq_iff hden).mp (RatFunc.num_div_denom r)
  have hmap := congrArg (algebraMap F[X] (RatFunc F)) hzero
  simp only [map_add, map_mul, RatFunc.algebraMap_X, map_zero] at hmap
  rw [hnum] at hmap
  apply hdiff
  exact (mul_eq_zero.mp (show
    (RatFunc.X + r) * algebraMap F[X] (RatFunc F) r.denom = 0 by
      linear_combination hmap)).resolve_right hden

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[num_natDegree_div_of_isCoprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma num_natDegree_div_of_isCoprime (p q : F[X])
  (hp : p ≠ 0) (hq : q ≠ 0) (hcop : IsCoprime p q) :
  (RatFunc.num
    (algebraMap F[X] (RatFunc F) p /
      algebraMap F[X] (RatFunc F) q)).natDegree = p.natDegree := by
  rw [charTwo_natDegree_num_div p q hq]
  have hgUnit : IsUnit (gcd p q) :=
    hcop.isUnit_of_dvd' (gcd_dvd_left _ _) (gcd_dvd_right _ _)
  have hg : gcd p q ≠ 0 := hgUnit.ne_zero
  have hmul : gcd p q * (p / gcd p q) = p :=
    EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left _ _)
  have hquot : p / gcd p q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact hp hmul.symm
  have hdegree := Polynomial.natDegree_mul hg hquot
  rwa [hmul, Polynomial.natDegree_eq_zero_of_isUnit hgUnit, zero_add] at hdegree

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryPoint_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryPoint_sub_one [Finite F] [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] (n : ℤ) :
  ordinaryPoint W (n - 1) = ordinaryPoint W n - ordinaryQ W := by
  have hstep := ordinaryPoint_add_one W (n - 1)
  rw [show n - 1 + 1 = n by ring] at hstep
  rw [hstep]
  abel

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryQ_y_ne_negY](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryQ_y_ne_negY [CharP F 2]
  (W : WeierstrassCurve F) :
  (0 : RatFunc F) ≠
    (ordinaryTwist W).toAffine.negY (RatFunc.X ^ 3) 0 := by
  simp only [WeierstrassCurve.Affine.negY, ordinaryTwist, zero_add,
    sub_eq_add_neg, CharTwo.neg_eq]
  simpa only [add_zero] using
    (mul_ne_zero (RatFunc.X_ne_zero (K := F))
      (pow_ne_zero 3 (RatFunc.X_ne_zero (K := F)))).symm

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryPaperX_doubleQ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryPaperX_doubleQ [CharP F 2]
  (W : WeierstrassCurve F) :
  ordinaryPaperX
    ((ordinaryTwist W).toAffine.addX (RatFunc.X ^ 3) (RatFunc.X ^ 3)
      ((ordinaryTwist W).toAffine.slope (RatFunc.X ^ 3)
        (RatFunc.X ^ 3) 0 0)) =
    algebraMap F[X] (RatFunc F) (ordinaryDoubleNumerator W) /
      algebraMap F[X] (RatFunc F) (X ^ 2) := by
  rw [(ordinaryTwist W).toAffine.slope_of_Y_ne rfl
    (ordinaryQ_y_ne_negY W)]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
    ordinaryTwist, ordinaryPaperX, map_add, map_pow, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C, ordinaryDoubleNumerator, zero_add,
    sub_eq_add_neg, CharTwo.neg_eq]
  field_simp [RatFunc.X_ne_zero]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, zero_add, add_zero]
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryDoubleNumerator_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryDoubleNumerator_natDegree (W : WeierstrassCurve F) :
  (ordinaryDoubleNumerator W).natDegree = 4 := by
  unfold ordinaryDoubleNumerator
  compute_degree
  norm_num

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinaryDoubleNumerator_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinaryDoubleNumerator_coprime [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
  IsCoprime (ordinaryDoubleNumerator W) (X ^ 2) := by
  have hb : W.a₆ ≠ 0 := by
    have h := W.Δ'.ne_zero
    rwa [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
  refine ⟨C W.a₆⁻¹, C W.a₆⁻¹ * X ^ 2, ?_⟩
  unfold ordinaryDoubleNumerator
  have hinv : C W.a₆⁻¹ * C W.a₆ = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hb, C_1]
  have htwo : (2 : F[X]) = 0 := CharTwo.two_eq_zero
  linear_combination hinv + X ^ 4 * C W.a₆⁻¹ * htwo

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[ordinary_num_natDegree_doubleQ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinary_num_natDegree_doubleQ [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
  (RatFunc.num
    (algebraMap F[X] (RatFunc F) (ordinaryDoubleNumerator W) /
      algebraMap F[X] (RatFunc F) (X ^ 2))).natDegree = 4 := by
  rw [num_natDegree_div_of_isCoprime _ _
    (by
      intro hzero
      have hdegree := ordinaryDoubleNumerator_natDegree W
      rw [hzero] at hdegree
      norm_num at hdegree)
    (pow_ne_zero 2 X_ne_zero) (ordinaryDoubleNumerator_coprime W)]
  exact ordinaryDoubleNumerator_natDegree W

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superPoint_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superPoint_add_one [Finite F] [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] (n : ℤ) :
  superPoint W (n + 1) = superPoint W n + superQ W := by
  rw [superPoint, superPoint, add_one_zsmul]
  abel

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superQ_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superQ_ne_zero [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
  superQ W ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero _

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superD_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superD_zero [Finite F] [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
  superD W 0 = Nat.card F := by
  rw [superD, superPoint]
  simp only [zero_zsmul, add_zero, superPZero, WeierstrassCurve.Affine.Point.mk,
    superPZeroX]
  change (RatFunc.num ((algebraMap F[X] (RatFunc F) X) ^ Nat.card F)).natDegree =
    Nat.card F
  rw [← map_pow, RatFunc.num_algebraMap, Polynomial.natDegree_X_pow]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[super_num_degree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma super_num_degree [Finite F] [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
  {x y : RatFunc F} (hxy : (superTwist W).toAffine.Nonsingular x y) :
  (RatFunc.denom x).natDegree < (RatFunc.num x).natDegree := by
  have ha : W.a₃ ≠ 0 := by
    have h := W.Δ'.ne_zero
    rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJEqZeroNF_of_char_two] at h
    intro ha
    apply h
    simp [ha]
  have hCa : RatFunc.C W.a₃ ≠ 0 := by
    intro hzero
    apply ha
    apply RatFunc.C_injective
    simpa using hzero
  have heq :
    y ^ 2 + RatFunc.C W.a₃ * y =
      x ^ 3 + RatFunc.C W.a₄ * x +
        RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X := by
    have heq' := hxy.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq'
    simp only [superTwist, zero_mul, add_zero] at heq'
    linear_combination heq'
  have hxpos : 0 < x.intDegree := by
    by_contra hxnot
    have hx : x.intDegree ≤ 0 := le_of_not_gt hxnot
    let lower := x ^ 3 + RatFunc.C W.a₄ * x + RatFunc.C W.a₄ * RatFunc.X
    have hx3 : (x ^ 3).intDegree ≤ 0 := intDegree_pow_le_zero hx 3
    have hbx : (RatFunc.C W.a₄ * x).intDegree ≤ 0 := by
      simpa using intDegree_mul_le_of_le (x := RatFunc.C W.a₄) (y := x)
        (m := 0) (n := 0) (by norm_num) (by simp) hx
    have hbX : (RatFunc.C W.a₄ * RatFunc.X).intDegree ≤ 1 := by
      simpa using intDegree_mul_le_of_le
        (x := RatFunc.C W.a₄) (y := RatFunc.X)
        (m := 0) (n := 1) (by norm_num) (by simp) (by simp)
    have hlower : lower.intDegree ≤ 1 := by
      dsimp only [lower]
      have hfirst := intDegree_add_le_of_le (m := 1) (by norm_num)
        (hx3.trans (by norm_num)) (hbx.trans (by norm_num))
      exact intDegree_add_le_of_le (m := 1) (by norm_num) hfirst hbX
    have hX3 : (RatFunc.X ^ 3 : RatFunc F).intDegree = 3 := by
      rw [intDegree_pow RatFunc.X_ne_zero]
      norm_num
    have hrhs : (RatFunc.X ^ 3 + lower).intDegree = 3 := by
      rw [intDegree_add_eq_left_of_lt (pow_ne_zero 3 RatFunc.X_ne_zero)]
      · exact hX3
      · rw [hX3]
        omega
    have heq' :
      y ^ 2 + RatFunc.C W.a₃ * y = RatFunc.X ^ 3 + lower := by
      dsimp only [lower]
      linear_combination heq
    by_cases hy0 : y = 0
    · subst y
      have hrhs0 : RatFunc.X ^ 3 + lower = 0 := by
        simpa using heq'.symm
      rw [hrhs0] at hrhs
      norm_num at hrhs
    by_cases hy : y.intDegree ≤ 0
    · have hy2 : (y ^ 2).intDegree ≤ 0 := intDegree_pow_le_zero hy 2
      have hay : (RatFunc.C W.a₃ * y).intDegree ≤ 0 := by
        simpa using intDegree_mul_le_of_le (x := RatFunc.C W.a₃) (y := y)
          (m := 0) (n := 0) (by norm_num) (by simp) hy
      have hlhs : (y ^ 2 + RatFunc.C W.a₃ * y).intDegree ≤ 0 :=
        intDegree_add_le_of_le (m := 0) (by norm_num) hy2 hay
      have hdegrees := congrArg RatFunc.intDegree heq'
      rw [hrhs] at hdegrees
      omega
    · have hypos : 0 < y.intDegree := lt_of_not_ge hy
      have hy2 : (y ^ 2).intDegree = 2 * y.intDegree := by
        rw [intDegree_pow hy0]
        norm_num
      have hay : (RatFunc.C W.a₃ * y).intDegree = y.intDegree := by
        rw [RatFunc.intDegree_mul hCa hy0]
        simp
      have hlhs :
        (y ^ 2 + RatFunc.C W.a₃ * y).intDegree = 2 * y.intDegree := by
        rw [intDegree_add_eq_left_of_lt (pow_ne_zero 2 hy0), hy2]
        rw [hay]
        omega
      have hdegrees := congrArg RatFunc.intDegree heq'
      rw [hlhs, hrhs] at hdegrees
      omega
  unfold RatFunc.intDegree at hxpos
  omega

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superD_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superD_eq_zero_iff [Finite F] [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
  (n : ℤ) :
  superD W n = 0 ↔ superPoint W n = 0 := by
  cases hp : superPoint W n with
  | zero =>
    constructor
    · exact fun _ ↦ WeierstrassCurve.Affine.Point.zero_def.symm
    · intro _
      simp [superD, hp]
  | some x y hxy =>
    have hdeg := super_num_degree W hxy
    constructor
    · intro hd
      simp only [superD, hp] at hd
      omega
    · exact fun hpzero ↦ (WeierstrassCurve.Affine.Point.some_ne_zero hxy hpzero).elim

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superNoAdjacentZeros](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superNoAdjacentZeros [Finite F] [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
  : ∀ n, superD W n = 0 → superD W (n + 1) = 0 → False := by
  intro n hn hn1
  have hp := (superD_eq_zero_iff W n).mp hn
  have hp1 := (superD_eq_zero_iff W (n + 1)).mp hn1
  apply superQ_ne_zero W
  have hs := superPoint_add_one W n
  rw [hp, hp1] at hs
  simpa using hs.symm

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superH_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superH_natDegree (W : WeierstrassCurve F) :
  (superH W).natDegree = 3 := by
  unfold superH
  compute_degree <;> norm_num

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[frobeniusTail_super_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma frobeniusTail_super_natDegree
  (W : WeierstrassCurve F) (e : ℕ) (he : 0 < e) :
  (frobeniusTail (superH W) (C W.a₃) e).natDegree =
    3 * 2 ^ (e - 1) := by
  induction e using Nat.twoStepInduction with
  | zero => omega
  | one => simp [frobeniusTail, superH_natDegree]
  | more e ih ih1 =>
    rw [frobeniusTail]
    have htail : frobeniusTail (superH W) (C W.a₃) (e + 1) ≠ 0 := by
      intro hzero
      have hdegree := ih1 (by omega)
      rw [hzero] at hdegree
      simp at hdegree
    rw [natDegree_add_eq_left_of_natDegree_lt]
    · rw [natDegree_pow, ih1 (by omega)]
      simp [pow_succ]
      ring
    · calc
      (C W.a₃ ^ (2 ^ (e + 2) - 2) * superH W).natDegree =
        (C (W.a₃ ^ (2 ^ (e + 2) - 2)) * superH W).natDegree := by
          rw [map_pow]
      _ ≤ (superH W).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ = 3 := superH_natDegree W
      _ < (frobeniusTail (superH W) (C W.a₃) (e + 1) ^ 2).natDegree := by
        rw [natDegree_pow, ih1 (by omega)]
        rw [show e + 1 - 1 = e by omega]
        have hpow : 0 < 2 ^ e := pow_pos (by norm_num) e
        nlinarith

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[eval_superV](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma eval_superV [Finite F] (W : WeierstrassCurve F) (x : F) :
  (superV W).eval x =
    frobeniusValue ((superH W).eval x) W.a₃
      (charTwoExponent (F := F)) := by
  simp only [superV, eval_frobeniusTail, eval_C]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[eval_superMinusOneNumerator](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma eval_superMinusOneNumerator [Finite F] [CharP F 2]
  (W : WeierstrassCurve F) (x : F) :
  (superMinusOneNumerator W).eval x =
    W.a₃ * frobeniusValue ((superH W).eval x) W.a₃
      (charTwoExponent (F := F)) + W.a₃ ^ 2 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hxq : x ^ Nat.card F = x := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card x
  have hx2q1 : x ^ (2 * Nat.card F + 1) = x ^ 3 := by
    calc
      x ^ (2 * Nat.card F + 1) = x ^ (2 * Nat.card F) * x := pow_succ _ _
      _ = (x ^ Nat.card F) ^ 2 * x := by
        rw [show 2 * Nat.card F = Nat.card F * 2 by omega, pow_mul]
      _ = x ^ 3 := by rw [hxq]; ring
  have hxq2 : x ^ (Nat.card F + 2) = x ^ 3 := by
    rw [pow_add, hxq]
    ring
  simp only [superMinusOneNumerator, eval_add, eval_mul, eval_pow, eval_X,
    eval_C, eval_superV, hx2q1, hxq2, hxq]
  have hcancel₁ : x ^ 3 + x ^ 3 = 0 := CharTwo.add_self_eq_zero _
  have hcancel₂ : W.a₄ * (x + x) = 0 := by rw [CharTwo.add_self_eq_zero, mul_zero]
  linear_combination hcancel₁ + hcancel₂

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superPointCount_eq_fiber_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superPointCount_eq_fiber_sum [Fintype F] [CharP F 2]
  (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF] [W.IsElliptic] :
  Nat.card W.toAffine.Point =
    (∑ x : F, Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) + 1 := by
  rw [W.toAffine.natCard_point_eq_natCard_affineSolutions_add_one]
  rw [Nat.card_congr (affineSolutionsEquivSuperFibers W), Nat.card_sigma]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superPZeroX_ne_QX](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superPZeroX_ne_QX [Finite F] :
  superPZeroX (F := F) ≠ RatFunc.X := by
  intro heq
  have hdegree := congrArg RatFunc.intDegree heq
  simp only [superPZeroX] at hdegree
  rw [intDegree_pow RatFunc.X_ne_zero] at hdegree
  simp only [RatFunc.intDegree_X, mul_one] at hdegree
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  omega

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superH_derivative](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superH_derivative [CharP F 2] (W : WeierstrassCurve F) :
  (superH W).derivative = X ^ 2 + C W.a₄ := by
  unfold superH
  simp only [derivative_add, derivative_mul, derivative_pow, derivative_X,
    derivative_C]
  have htwo : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
  have hthree : ((3 : ℕ) : F) = 1 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, Nat.cast_add, htwo,
      Nat.cast_one, zero_add]
  rw [hthree, map_one]
  norm_num

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[derivative_frobeniusTail_super](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma derivative_frobeniusTail_super [CharP F 2]
  (W : WeierstrassCurve F) (e : ℕ) (he : 0 < e) :
  (frobeniusTail (superH W) (C W.a₃) e).derivative =
    C (W.a₃ ^ (2 ^ e - 2)) * (X ^ 2 + C W.a₄) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
  rw [frobeniusTail, derivative_add, derivative_pow, derivative_mul,
    derivative_pow, derivative_C, superH_derivative]
  have htwo : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
  rw [htwo, map_zero]
  norm_num

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[rootMultiplicity_superNumerator_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma rootMultiplicity_superNumerator_eq_zero [Finite F]
  [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
  [W.IsCharTwoJEqZeroNF] (x : F)
  (hvalue : frobeniusValue ((superH W).eval x) W.a₃
    (charTwoExponent (F := F)) = 0) :
  Polynomial.rootMultiplicity x (superMinusOneNumerator W) = 0 := by
  apply Polynomial.rootMultiplicity_eq_zero
  intro hroot
  have heval := eval_superMinusOneNumerator W x
  rw [hvalue, mul_zero, zero_add] at heval
  exact (pow_ne_zero 2 (super_a₃_ne_zero W)) (heval.symm.trans hroot)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[super_product_formula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma super_product_formula {R : Type*} [CommRing R] [CharP R 2]
  (t f g a b z : R)
  (curve : z ^ 2 + a * g ^ 2 * z + f ^ 3 * g + b * f * g ^ 3 +
    t ^ 3 * g ^ 4 + b * t * g ^ 4 = 0) :
  ((t * f + b * g) * (t * g + f) + a * z + a ^ 2 * g ^ 2) *
    ((t * f + b * g) * (t * g + f) + a * z) =
    (t ^ 2 * f ^ 2 + b ^ 2 * g ^ 2 + a ^ 2 * g * (t * g + f)) *
      (t * g + f) ^ 2 := by
  have htwo : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination a ^ 2 * curve +
    (-t * f ^ 2 * g ^ 2 * a ^ 2 + t * f ^ 2 * a * z +
      t * f ^ 3 * b * g + t * b * g ^ 2 * a * z + t ^ 2 * f * g * a * z -
      t ^ 2 * f * g ^ 3 * a ^ 2 + 2 * t ^ 2 * f ^ 2 * b * g ^ 2 +
      t ^ 3 * f * b * g ^ 3 - t ^ 3 * g ^ 4 * a ^ 2 +
      f * b * g * a * z - f ^ 3 * g * a ^ 2) * htwo

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superNeighborFirst_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superNeighborFirst_natDegree
  (W : WeierstrassCurve F) {f g : F[X]} (hf : f ≠ 0)
  (hdegree : g.natDegree < f.natDegree) :
  (superNeighborFirst W f g).natDegree = 2 * f.natDegree + 2 := by
  have hXf : (X * f).natDegree = f.natDegree + 1 := by
    rw [Polynomial.natDegree_mul X_ne_zero hf, Polynomial.natDegree_X]
    omega
  have hmain : ((X * f) ^ 2).natDegree = 2 * f.natDegree + 2 := by
    rw [Polynomial.natDegree_pow, hXf]
    omega
  have hfirst : (C (W.a₄ ^ 2) * g ^ 2).natDegree ≤ 2 * g.natDegree := by
    calc
      (C (W.a₄ ^ 2) * g ^ 2).natDegree ≤ (g ^ 2).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ = 2 * g.natDegree := Polynomial.natDegree_pow _ _
  have hXg : (X * g).natDegree ≤ f.natDegree := by
    calc
      (X * g).natDegree ≤ X.natDegree + g.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ f.natDegree := by rw [Polynomial.natDegree_X]; omega
  have hD : (X * g + f).natDegree ≤ f.natDegree :=
    (Polynomial.natDegree_add_le _ _).trans (max_le hXg le_rfl)
  have hsecond :
    (C (W.a₃ ^ 2) * g * (X * g + f)).natDegree ≤
      g.natDegree + f.natDegree := by
    calc
      (C (W.a₃ ^ 2) * g * (X * g + f)).natDegree ≤
        (C (W.a₃ ^ 2) * g).natDegree + (X * g + f).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ g.natDegree + f.natDegree :=
        Nat.add_le_add (Polynomial.natDegree_C_mul_le _ _) hD
  have hremainder :
    (C (W.a₄ ^ 2) * g ^ 2 +
      C (W.a₃ ^ 2) * g * (X * g + f)).natDegree <
        2 * f.natDegree + 2 := by
    apply (Polynomial.natDegree_add_le _ _).trans_lt
    rw [max_lt_iff]
    constructor <;> omega
  unfold superNeighborFirst
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact hmain
  · rwa [hmain]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superNeighbor_primitive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superNeighbor_primitive [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
  {f g : F[X]} (hfg : IsCoprime f g) (hden : X * g + f ≠ 0) :
  PrimitiveTriple (superNeighborFirst W f g) (superNeighborSecond W g)
    (neighborDenominator f g) := by
  have ha := super_a₃_ne_zero W
  apply primitiveTriple_of_no_common_irreducible (pow_ne_zero 2 hden)
  intro p hp _hpFirst hpSecond hpDen
  have hprime := hp.prime
  have hpD : p ∣ X * g + f := hprime.dvd_of_dvd_pow hpDen
  have hpG : p ∣ g := by
    have hpProduct : p ∣ C (W.a₃ ^ 2) * g ^ 2 := hpSecond
    obtain hpC | hpg := hprime.dvd_mul.mp hpProduct
    · have hCunit : IsUnit (C (W.a₃ ^ 2)) :=
      Polynomial.isUnit_C.mpr
        (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 ha))
      exact (hprime.not_dvd_one
        (hpC.trans (isUnit_iff_dvd_one.mp hCunit))).elim
    · exact hprime.dvd_of_dvd_pow hpg
  have hpF : p ∣ f := by
    have hdifference := hpD.sub (hpG.mul_left X)
    convert hdifference using 1
    ring
  exact hp.not_isUnit (hfg.isUnit_of_dvd' hpF hpG)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superNeighborFirst_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superNeighborFirst_ratio (W : WeierstrassCurve F)
  (r : RatFunc F) :
  algebraMap F[X] (RatFunc F) (superNeighborFirst W r.num r.denom) /
    algebraMap F[X] (RatFunc F) (neighborDenominator r.num r.denom) =
    (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C (W.a₄ ^ 2) +
      RatFunc.C (W.a₃ ^ 2) * (RatFunc.X + r)) /
        (RatFunc.X + r) ^ 2 := by
  simp only [superNeighborFirst, neighborDenominator, map_add, map_mul,
    map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  let d := algebraMap F[X] (RatFunc F) r.denom
  have hd : d ≠ 0 := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum : algebraMap F[X] (RatFunc F) r.num = r * d :=
    (div_eq_iff hd).mp (RatFunc.num_div_denom r)
  change
    ((RatFunc.X * algebraMap F[X] (RatFunc F) r.num) ^ 2 +
      (RatFunc.C W.a₄ ^ 2 * d ^ 2 +
        RatFunc.C W.a₃ ^ 2 * d *
          (RatFunc.X * d + algebraMap F[X] (RatFunc F) r.num))) /
      (RatFunc.X * d + algebraMap F[X] (RatFunc F) r.num) ^ 2 = _
  rw [hnum]
  rw [show
    (RatFunc.X * (r * d)) ^ 2 + (RatFunc.C W.a₄ ^ 2 * d ^ 2 +
      RatFunc.C W.a₃ ^ 2 * d * (RatFunc.X * d + r * d)) =
      d ^ 2 * (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C W.a₄ ^ 2 +
        RatFunc.C W.a₃ ^ 2 * (RatFunc.X + r)) by ring]
  rw [show (RatFunc.X * d + r * d) ^ 2 =
    d ^ 2 * (RatFunc.X + r) ^ 2 by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hd)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superNeighborSecond_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superNeighborSecond_ratio (W : WeierstrassCurve F)
  (r : RatFunc F) :
  algebraMap F[X] (RatFunc F) (superNeighborSecond W r.denom) /
    algebraMap F[X] (RatFunc F) (neighborDenominator r.num r.denom) =
    RatFunc.C (W.a₃ ^ 2) / (RatFunc.X + r) ^ 2 := by
  simp only [superNeighborSecond, neighborDenominator, map_add, map_mul,
    map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  let d := algebraMap F[X] (RatFunc F) r.denom
  have hd : d ≠ 0 := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum : algebraMap F[X] (RatFunc F) r.num = r * d :=
    (div_eq_iff hd).mp (RatFunc.num_div_denom r)
  change
    RatFunc.C W.a₃ ^ 2 * d ^ 2 /
      (RatFunc.X * d + algebraMap F[X] (RatFunc F) r.num) ^ 2 = _
  rw [hnum]
  rw [show (RatFunc.X * d + r * d) ^ 2 =
    d ^ 2 * (RatFunc.X + r) ^ 2 by ring]
  rw [show RatFunc.C W.a₃ ^ 2 * d ^ 2 =
    d ^ 2 * RatFunc.C W.a₃ ^ 2 by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hd)

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[super_neighbor_plus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma super_neighbor_plus [CharP F 2]
  (W : WeierstrassCurve F) {r s : RatFunc F}
  (heq : s ^ 2 + RatFunc.C W.a₃ * s =
    r ^ 3 + RatFunc.C W.a₄ * r +
      RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X)
  (hdiff : RatFunc.X + r ≠ 0) :
  (s / (r - RatFunc.X)) ^ 2 + r + RatFunc.X =
    ((RatFunc.X * r + RatFunc.C W.a₄) * (RatFunc.X + r) +
      RatFunc.C W.a₃ * s) / (RatFunc.X + r) ^ 2 := by
  have hdiffEq : r - RatFunc.X = RatFunc.X + r := by
    simp only [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  have hs2 : s ^ 2 =
    r ^ 3 + RatFunc.C W.a₄ * r +
      RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X +
        RatFunc.C W.a₃ * s := by
    calc
      s ^ 2 = (s ^ 2 + RatFunc.C W.a₃ * s) +
        RatFunc.C W.a₃ * s := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = _ := by rw [heq]
  rw [div_pow, hs2, hdiffEq]
  field_simp [hdiff]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, add_zero]
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[super_neighbor_minus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma super_neighbor_minus [CharP F 2]
  (W : WeierstrassCurve F) {r s : RatFunc F}
  (heq : s ^ 2 + RatFunc.C W.a₃ * s =
    r ^ 3 + RatFunc.C W.a₄ * r +
      RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X)
  (hdiff : RatFunc.X + r ≠ 0) :
  ((s + RatFunc.C W.a₃) / (r - RatFunc.X)) ^ 2 + r + RatFunc.X =
    ((RatFunc.X * r + RatFunc.C W.a₄) * (RatFunc.X + r) +
      RatFunc.C W.a₃ * s + RatFunc.C (W.a₃ ^ 2)) /
        (RatFunc.X + r) ^ 2 := by
  have hdiffEq : r - RatFunc.X = RatFunc.X + r := by
    simp only [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  have hs2 : s ^ 2 =
    r ^ 3 + RatFunc.C W.a₄ * r +
      RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X +
        RatFunc.C W.a₃ * s := by
    calc
      s ^ 2 = (s ^ 2 + RatFunc.C W.a₃ * s) +
        RatFunc.C W.a₃ * s := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = _ := by rw [heq]
  have hsum2 : (s + RatFunc.C W.a₃) ^ 2 =
    r ^ 3 + RatFunc.C W.a₄ * r +
      RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X +
        RatFunc.C W.a₃ * s + RatFunc.C (W.a₃ ^ 2) := by
    calc
      (s + RatFunc.C W.a₃) ^ 2 = s ^ 2 + RatFunc.C (W.a₃ ^ 2) := by
        rw [add_sq, show (2 : RatFunc F) = 0 from CharTwo.two_eq_zero]
        simp only [zero_mul, add_zero, ← map_pow]
      _ = _ := by rw [hs2]
  rw [div_pow, hsum2, hdiffEq]
  field_simp [hdiff]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, add_zero]
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[super_neighbor_pair_product](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma super_neighbor_pair_product [CharP F 2]
  (W : WeierstrassCurve F) {r s : RatFunc F}
  (heq : s ^ 2 + RatFunc.C W.a₃ * s =
    r ^ 3 + RatFunc.C W.a₄ * r +
      RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X)
  (hdiff : RatFunc.X + r ≠ 0) :
  ((s / (r - RatFunc.X)) ^ 2 + r + RatFunc.X) *
    (((s + RatFunc.C W.a₃) / (r - RatFunc.X)) ^ 2 + r + RatFunc.X) =
    (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C (W.a₄ ^ 2) +
      RatFunc.C (W.a₃ ^ 2) * (RatFunc.X + r)) /
        (RatFunc.X + r) ^ 2 := by
  rw [super_neighbor_plus W heq hdiff, super_neighbor_minus W heq hdiff]
  have hcurve :
    s ^ 2 + RatFunc.C W.a₃ * s + r ^ 3 +
      RatFunc.C W.a₄ * r + RatFunc.X ^ 3 +
        RatFunc.C W.a₄ * RatFunc.X = 0 := by
    calc
      _ = (s ^ 2 + RatFunc.C W.a₃ * s) +
        (r ^ 3 + RatFunc.C W.a₄ * r + RatFunc.X ^ 3 +
          RatFunc.C W.a₄ * RatFunc.X) := by ring
      _ = (r ^ 3 + RatFunc.C W.a₄ * r + RatFunc.X ^ 3 +
        RatFunc.C W.a₄ * RatFunc.X) +
        (r ^ 3 + RatFunc.C W.a₄ * r + RatFunc.X ^ 3 +
          RatFunc.C W.a₄ * RatFunc.X) := by rw [heq]
      _ = 0 := CharTwo.add_self_eq_zero _
  have hformula := super_product_formula RatFunc.X r 1
    (RatFunc.C W.a₃) (RatFunc.C W.a₄) s (by simpa using hcurve)
  simp only [map_pow] at ⊢
  simp only [mul_one, one_pow] at hformula
  field_simp [hdiff]
  linear_combination hformula

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[super_neighbor_pair_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma super_neighbor_pair_sum [CharP F 2]
  (W : WeierstrassCurve F) {r s : RatFunc F}
  (hdiff : RatFunc.X + r ≠ 0) :
  ((s / (r - RatFunc.X)) ^ 2 + r + RatFunc.X) +
    (((s + RatFunc.C W.a₃) / (r - RatFunc.X)) ^ 2 + r + RatFunc.X) =
    RatFunc.C (W.a₃ ^ 2) / (RatFunc.X + r) ^ 2 := by
  have hdiff' : r - RatFunc.X ≠ 0 := by
    simpa only [sub_eq_add_neg, CharTwo.neg_eq, add_comm] using hdiff
  field_simp [hdiff, hdiff']
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    CharTwo.neg_eq, sub_eq_add_neg, mul_zero, zero_add, add_zero,
    ← map_pow]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[super_coordinates_equation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma super_coordinates_equation [CharP F 2]
  (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF]
  {x y : RatFunc F} (hxy : (superTwist W).toAffine.Nonsingular x y) :
  y ^ 2 + RatFunc.C W.a₃ * y =
    x ^ 3 + RatFunc.C W.a₄ * x +
      RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X := by
  have heq := hxy.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [superTwist, zero_mul, add_zero] at heq
  linear_combination heq

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superPoint_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superPoint_sub_one [Finite F] [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] (n : ℤ) :
  superPoint W (n - 1) = superPoint W n - superQ W := by
  have hstep := superPoint_add_one W (n - 1)
  rw [show n - 1 + 1 = n by ring] at hstep
  rw [hstep]
  abel

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superQ_y_ne_negY](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superQ_y_ne_negY [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
  (0 : RatFunc F) ≠ (superTwist W).toAffine.negY RatFunc.X 0 := by
  simp only [WeierstrassCurve.Affine.negY, superTwist, zero_mul, zero_add,
    sub_eq_add_neg, CharTwo.neg_eq]
  intro hzero
  apply super_a₃_ne_zero W
  apply RatFunc.C_injective
  simpa using hzero.symm

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superX_doubleQ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superX_doubleQ [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
  (superTwist W).toAffine.addX RatFunc.X RatFunc.X
    ((superTwist W).toAffine.slope RatFunc.X RatFunc.X 0 0) =
    algebraMap F[X] (RatFunc F) (superDoubleNumerator W) /
      algebraMap F[X] (RatFunc F) (superDoubleDenominator W) := by
  rw [(superTwist W).toAffine.slope_of_Y_ne rfl (superQ_y_ne_negY W)]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
    superTwist, superDoubleNumerator, superDoubleDenominator, map_add,
    map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, zero_mul, zero_add,
    sub_eq_add_neg, CharTwo.neg_eq]
  have haC : RatFunc.C W.a₃ ≠ 0 := by
    intro hzero
    apply super_a₃_ne_zero W
    apply RatFunc.C_injective
    simpa using hzero
  field_simp [haC]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, zero_add, add_zero]
  ring

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superDoubleNumerator_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superDoubleNumerator_natDegree (W : WeierstrassCurve F) :
  (superDoubleNumerator W).natDegree = 4 := by
  unfold superDoubleNumerator
  compute_degree
  norm_num

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superDoubleDenominator_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superDoubleDenominator_ne_zero [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
  superDoubleDenominator W ≠ 0 :=
Polynomial.C_ne_zero.mpr (pow_ne_zero 2 (super_a₃_ne_zero W))

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[superDouble_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma superDouble_coprime [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
  IsCoprime (superDoubleNumerator W) (superDoubleDenominator W) := by
  have ha2 : W.a₃ ^ 2 ≠ 0 := pow_ne_zero 2 (super_a₃_ne_zero W)
  refine ⟨0, C (W.a₃ ^ 2)⁻¹, ?_⟩
  simp only [zero_mul, zero_add, superDoubleDenominator]
  rw [← C_mul, inv_mul_cancel₀ ha2, C_1]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]
/--
[super_num_natDegree_doubleQ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma super_num_natDegree_doubleQ [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
  (RatFunc.num
    (algebraMap F[X] (RatFunc F) (superDoubleNumerator W) /
      algebraMap F[X] (RatFunc F) (superDoubleDenominator W))).natDegree = 4 := by
  rw [num_natDegree_div_of_isCoprime _ _
    (by
      intro hzero
      have hdegree := superDoubleNumerator_natDegree W
      rw [hzero] at hdegree
      norm_num at hdegree)
    (superDoubleDenominator_ne_zero W) (superDouble_coprime W)]
  exact superDoubleNumerator_natDegree W

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

/--
[hasse_bound_of_isCharTwoNF](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
lemma hasse_bound_of_isCharTwoNF
  {F : Type u} [Field F] [Finite F] [CharP F 2]
  {W : WeierstrassCurve F} [W.IsElliptic] [W.IsCharTwoNF] :
-- imply
  (((Nat.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤
    4 * (Nat.card F : ℤ)) :=
-- proof
  (Classical.choice (manin_degree_data_of_isCharTwoNF W)).hasse_bound

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

/--
[hasse_bound_of_isCharTwoJNeZeroNF](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
lemma hasse_bound_of_isCharTwoJNeZeroNF
  {F : Type u} [Field F] [Finite F] [CharP F 2]
  {W : WeierstrassCurve F} [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
-- imply
  (((Nat.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤
    4 * (Nat.card F : ℤ)) := by
-- proof
  let _ : W.IsCharTwoNF := .of_j_ne_zero
  exact hasse_bound_of_isCharTwoNF W

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

/--
[hasse_bound_of_isCharTwoJEqZeroNF](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
lemma hasse_bound_of_isCharTwoJEqZeroNF
  {F : Type u} [Field F] [Finite F] [CharP F 2]
  {W : WeierstrassCurve F} [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
-- imply
  (((Nat.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤
    4 * (Nat.card F : ℤ)) := by
-- proof
  let _ : W.IsCharTwoNF := .of_j_eq_zero
  exact hasse_bound_of_isCharTwoNF W
end

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

/--
[ordinary_a₆_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma ordinary_a₆_ne_zero [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
  W.a₆ ≠ 0 := by
  have h := W.Δ'.ne_zero
  rwa [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJNeZeroNF_of_char_two] at h


namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

variable {F : Type u} [Field F]

/--
[super_a₃_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma super_a₃_ne_zero [CharP F 2]
  (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
  W.a₃ ≠ 0 := by
  have h := W.Δ'.ne_zero
  rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJEqZeroNF_of_char_two] at h
  intro ha
  apply h
  simp [ha]

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

/--
[manin_degree_data_of_isCharTwoNF](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean)
-/
@[path]
private lemma manin_degree_data_of_isCharTwoNF_eq
  {F : Type u} [Field F] [Finite F] [CharP F 2]
  {W : WeierstrassCurve F} [W.IsElliptic] [W.IsCharTwoNF] :
-- imply
  Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
    (Nat.card F) (Nat.card W.toAffine.Point)) := by
-- proof
  apply MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.manin_degree_data_of_isCharTwoNF W


-- created on 2026-10-20
-- updated on 2026-10-23
