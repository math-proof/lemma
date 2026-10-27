import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.FourierExpansion
open Finset BigOperators BooleanFourier


namespace BooleanFourier

/--
[boolToReal_true](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
lemma boolToReal_true :
-- imply
  boolToReal true = 1 := by
-- proof
  simp [boolToReal]

end BooleanFourier

namespace BooleanFourier

/--
[boolToReal_false](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
lemma boolToReal_false :
-- imply
  boolToReal false = -1 := by
-- proof
  simp [boolToReal]

end BooleanFourier

namespace BooleanFourier

/--
[boolToReal_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
lemma boolToReal_sq
  {b : Bool} :
-- imply
  boolToReal b ^ 2 = 1 := by
-- proof
  cases b <;> simp [boolToReal]

end BooleanFourier

namespace BooleanFourier

/--
[boolToReal_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
lemma boolToReal_ne_zero
  {b : Bool} :
-- imply
  boolToReal b ≠ 0 := by
-- proof
  cases b <;> simp [boolToReal]

end BooleanFourier

namespace BooleanFourier

/--
[boolToReal_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
lemma boolToReal_mul_self
  {b : Bool} :
-- imply
  boolToReal b * boolToReal b = 1 := by
-- proof
  cases b <;> simp [boolToReal]

end BooleanFourier

namespace BooleanFourier

/--
[boolToReal_not](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
lemma boolToReal_not
  {b : Bool} :
-- imply
  boolToReal (!b) = -boolToReal b := by
-- proof
  cases b <;> simp [boolToReal]

end BooleanFourier

namespace BooleanFourier

/--
[one_add_boolToReal_mul_boolToReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
lemma one_add_boolToReal_mul_boolToReal
  {a b : Bool} :
-- imply
  1 + boolToReal a * boolToReal b = if a = b then 2 else 0 := by
-- proof
  cases a <;> cases b <;> simp [boolToReal] <;> norm_num

end BooleanFourier

namespace BooleanFourier

/--
[chi_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
lemma chi_empty
  {n : ℕ}
  {x : Fin n → Bool} :
-- imply
  chi ∅ x = 1 := by
-- proof
  simp [chi]

end BooleanFourier

namespace BooleanFourier

/--
[chi_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
lemma chi_sq
  {n : ℕ}
  {S : Finset (Fin n)}
  {x : Fin n → Bool} :
-- imply
  chi S x ^ 2 = 1 := by
-- proof
  simp only [chi, ← Finset.prod_pow]
  simp [boolToReal_sq]

end BooleanFourier

namespace BooleanFourier

/--
[chi_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
lemma chi_mul_self
  {n : ℕ}
  {S : Finset (Fin n)}
  {x : Fin n → Bool} :
-- imply
  chi S x * chi S x = 1 := by
-- proof
  have h := chi_sq (S := S) (x := x)
  linarith [sq_abs (chi S x), h, sq_nonneg (chi S x)]

end BooleanFourier

namespace BooleanFourier

/--
[chi_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
lemma chi_ne_zero
  {n : ℕ}
  {S : Finset (Fin n)}
  {x : Fin n → Bool} :
-- imply
  chi S x ≠ 0 := by
-- proof
  simp only [chi]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => boolToReal_ne_zero (b := x i))

end BooleanFourier

namespace BooleanFourier

/--
[flipAt_flipAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
lemma flipAt_flipAt
  {n : ℕ}
  {j : Fin n}
  {x : Fin n → Bool} :
-- imply
  flipAt j (flipAt j x) = x := by
-- proof
  ext i
  simp only [flipAt, Function.update]
  split_ifs with h
  · subst h; simp
  · rfl

end BooleanFourier

namespace BooleanFourier

/--
[flipAt_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
lemma flipAt_ne_self
  {n : ℕ}
  {j : Fin n}
  {x : Fin n → Bool} :
-- imply
  flipAt j x ≠ x := by
-- proof
  intro h
  have := congr_fun h j
  simp [flipAt, Function.update_self] at this

end BooleanFourier

namespace BooleanFourier

/--
[chi_flipAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
lemma chi_flipAt
  {n : ℕ}
  {S : Finset (Fin n)}
  {j : Fin n}
  {x : Fin n → Bool}
-- given
  (hj : j ∈ S) :
-- imply
  chi S (flipAt j x) = -chi S x := by
-- proof
  simp only [chi, flipAt]
  have hlhs : ∏ i ∈ S, boolToReal (Function.update x j (!x j) i) =
    boolToReal (Function.update x j (!x j) j) *
    ∏ i ∈ S.erase j, boolToReal (Function.update x j (!x j) i) :=
    (Finset.mul_prod_erase S _ hj).symm
  have hrhs : ∏ i ∈ S, boolToReal (x i) =
    boolToReal (x j) * ∏ i ∈ S.erase j, boolToReal (x i) :=
    (Finset.mul_prod_erase S _ hj).symm
  rw [hlhs, hrhs]
  have h1 : boolToReal (Function.update x j (!x j) j) = -boolToReal (x j) := by
    simp [Function.update_self, boolToReal_not]
  have h2 : ∏ i ∈ S.erase j, boolToReal (Function.update x j (!x j) i) =
    ∏ i ∈ S.erase j, boolToReal (x i) := by
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    exact Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
  rw [h1, h2]
  ring

end BooleanFourier

namespace BooleanFourier

/--
[sum_chi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
lemma sum_chi
  {n : ℕ}
  {S : Finset (Fin n)} :
-- imply
  ∑ x : Fin n → Bool, chi S x = if S = ∅ then (2 : ℝ) ^ n else 0 := by
-- proof
  split_ifs with h
  · subst h
    simp [chi, Fintype.card_bool]
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr h
    apply Finset.sum_ninvolution (g := fun x => flipAt j x)
    · intro x
      have := chi_flipAt (S := S) (j := j) (x := x) hj
      linarith
    · intro x _
      exact flipAt_ne_self (j := j) (x := x)
    · intro x
      exact Finset.mem_univ _
    · intro x
      exact flipAt_flipAt (j := j) (x := x)

end BooleanFourier

namespace BooleanFourier

/--
[sum_chi_mul_chi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
lemma sum_chi_mul_chi
  {n : ℕ}
  {x y : Fin n → Bool} :
-- imply
  ∑ S : Finset (Fin n), chi S x * chi S y = if x = y then (2 : ℝ) ^ n else 0 := by
-- proof
  classical
  have hprod : ∀ S : Finset (Fin n),
    chi S x * chi S y = ∏ i ∈ S, (boolToReal (x i) * boolToReal (y i)) := by
    intro S
    simp only [chi, Finset.prod_mul_distrib]
  simp_rw [hprod]
  have hkey : ∑ S : Finset (Fin n),
    ∏ i ∈ S, (boolToReal (x i) * boolToReal (y i)) =
    ∏ i : Fin n, (1 + boolToReal (x i) * boolToReal (y i)) := by
    conv_lhs =>
      rw [show (∑ S : Finset (Fin n),
        ∏ i ∈ S, (boolToReal (x i) * boolToReal (y i))) =
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∏ i ∈ S, (boolToReal (x i) * boolToReal (y i)) from by
          rw [Finset.powerset_univ]]
    rw [← Finset.prod_one_add]
  rw [hkey]
  simp_rw [one_add_boolToReal_mul_boolToReal]
  split_ifs with h
  · subst h
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

end BooleanFourier

namespace BooleanFourier

/--
[fourier_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
lemma fourier_expansion
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {x : Fin n → Bool} :
-- imply
  f x = ∑ S : Finset (Fin n), fourierCoeff f S * chi S x := by
-- proof
  classical
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)
  simp only [fourierCoeff, one_div]
  have key : ∑ S : Finset (Fin n), ((2 : ℝ) ^ n)⁻¹ *
    (∑ y : Fin n → Bool, f y * chi S y) * chi S x =
    ((2 : ℝ) ^ n)⁻¹ * (f x * (2 : ℝ) ^ n) := by
    have step1 : ∑ S : Finset (Fin n), ((2 : ℝ) ^ n)⁻¹ *
      (∑ y : Fin n → Bool, f y * chi S y) * chi S x =
      ((2 : ℝ) ^ n)⁻¹ * ∑ S : Finset (Fin n),
        (∑ y : Fin n → Bool, f y * chi S y) * chi S x := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
    rw [step1]
    congr 1
    have step2 : ∑ S : Finset (Fin n),
      (∑ y : Fin n → Bool, f y * chi S y) * chi S x =
      ∑ S : Finset (Fin n),
        ∑ y : Fin n → Bool, f y * chi S y * chi S x := by
      congr 1; ext S; exact Finset.sum_mul (Finset.univ) _ _
    rw [step2, Finset.sum_comm]
    have step3 : ∑ y : Fin n → Bool,
      ∑ S : Finset (Fin n), f y * chi S y * chi S x =
      ∑ y : Fin n → Bool,
        f y * ∑ S : Finset (Fin n), chi S y * chi S x := by
      congr 1; ext y
      have : ∑ S : Finset (Fin n), f y * chi S y * chi S x =
        f y * ∑ S : Finset (Fin n), chi S y * chi S x := by
        simp_rw [show ∀ S : Finset (Fin n), f y * chi S y * chi S x =
          f y * (chi S y * chi S x) from fun S => by ring]
        rw [← Finset.mul_sum (a := f y) (s := Finset.univ)]
      exact this
    rw [step3]
    simp_rw [sum_chi_mul_chi, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ x]
    simp only [Finset.mem_univ, ite_true]
  rw [key]
  field_simp

end BooleanFourier


-- created on 2026-10-23
-- updated on 2026-10-27
