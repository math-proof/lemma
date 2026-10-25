import Mathlib
import sympy.Basic
import Instance.v1.Atlas.TensorCategories.code.HigherDerivation
open TensorCategories TensorCategories.HigherDerivationSystem


namespace TensorCategories

/--
[HigherDerivationSystem.χ_one_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
lemma HigherDerivationSystem.χ_one_mul
  {k : Type w} [Field k]
  {A : Type w} [Ring A] [Algebra k A]
  {ε : A →ₐ[k] k}
  {a b : A}
-- given
  (hds : HigherDerivationSystem k A ε) :
-- imply
  hds.χ 1 (a * b) = hds.χ 1 a * ε b + ε a * hds.χ 1 b := by
-- proof
  have h := hds.χ_mul 1 a b
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_self,
    Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, Nat.sub_self,
    zero_add] at h
  rw [hds.χ_zero] at h
  simp only [AlgHom.toLinearMap_apply] at h
  rw [h]; ring

end TensorCategories

namespace TensorCategories.HigherDerivationSystem

variable {k : Type w} [Field k] {A : Type w} [Ring A] [Algebra k A]
variable {ε : A →ₐ[k] k} (hds : HigherDerivationSystem k A ε)
/--
[χ_apply_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
lemma χ_apply_zero (a : A) : hds.χ 0 a = ε a := by
rw [hds.χ_zero]; rfl

end TensorCategories.HigherDerivationSystem

namespace TensorCategories.HigherDerivationSystem

variable {k : Type w} [Field k] {A : Type w} [Ring A] [Algebra k A]
variable {ε : A →ₐ[k] k} (hds : HigherDerivationSystem k A ε)
/--
[χ_one_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
lemma χ_one_one : hds.χ 1 1 = 0 := by
  have h := hds.χ_mul 1 1 1
  simp only [mul_one, Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_self,
    Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, Nat.sub_self, zero_add] at h
  rw [hds.χ_zero] at h
  simp only [AlgHom.toLinearMap_apply, map_one, one_mul, mul_one] at h
  have := sub_eq_zero.mpr h; simp at this; exact this

end TensorCategories.HigherDerivationSystem

namespace TensorCategories.HigherDerivationSystem

variable {k : Type w} [Field k] {A : Type w} [Ring A] [Algebra k A]
variable {ε : A →ₐ[k] k} (hds : HigherDerivationSystem k A ε)
/--
[χ_one_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
lemma χ_one_algebraMap (r : k) : hds.χ 1 (algebraMap k A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul_of_tower, hds.χ_one_one, smul_zero]

end TensorCategories.HigherDerivationSystem

namespace TensorCategories.HigherDerivationSystem

variable {k : Type w} [Field k] {A : Type w} [Ring A] [Algebra k A]
variable {ε : A →ₐ[k] k} (hds : HigherDerivationSystem k A ε)
/--
[χ_pow_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
lemma χ_pow_vanish {a : A} (ha : ε a = 0) (m n : ℕ) (hmn : m < n) :
  hds.χ m (a ^ n) = 0 := by
  induction n generalizing m with
  | zero => omega
  | succ n ih =>
    rw [pow_succ', hds.χ_mul m a (a ^ n)]
    apply Finset.sum_eq_zero
    intro j hj; rw [Finset.mem_range] at hj
    by_cases hj0 : j = 0
    · subst hj0; simp [hds.χ_apply_zero, ha]
    · rw [ih (m - j) (by omega)]; ring

end TensorCategories.HigherDerivationSystem

namespace TensorCategories.HigherDerivationSystem

variable {k : Type w} [Field k] {A : Type w} [Ring A] [Algebra k A]
variable {ε : A →ₐ[k] k} (hds : HigherDerivationSystem k A ε)
/--
[χ_pow_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
lemma χ_pow_diagonal {a : A} (ha : ε a = 0) (n : ℕ) :
  hds.χ n (a ^ n) = (n.factorial : k) * (hds.χ 1 a) ^ n := by
  induction n with
  | zero => simp [hds.χ_apply_zero, map_one]
  | succ n ih =>
    rw [pow_succ', hds.χ_mul (n + 1) a (a ^ n)]
    have hsum : ∀ j ∈ Finset.range (n + 2),
      ((n + 1).choose j : k) * hds.χ j a * hds.χ ((n + 1) - j) (a ^ n) =
      if j = 1 then (↑(n + 1) : k) * hds.χ 1 a * ((↑n.factorial : k) * (hds.χ 1 a) ^ n)
      else 0 := by
      intro j hj; rw [Finset.mem_range] at hj
      by_cases hj1 : j = 1
      · subst hj1; simp [Nat.choose_one_right, ih]
      · simp only [hj1, ite_false]
        by_cases hj0 : j = 0
        · subst hj0; simp [hds.χ_apply_zero, ha]
        · rw [hds.χ_pow_vanish ha _ n (by omega)]; ring
    rw [Finset.sum_congr rfl hsum, Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    rw [if_pos (by omega : 1 < n + 2), Nat.factorial_succ, Nat.cast_mul, pow_succ]; ring

end TensorCategories.HigherDerivationSystem

namespace TensorCategories.HigherDerivationSystem

/--
[coeff_zero_of_sum_pow_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
lemma coeff_zero_of_sum_pow_eq_zero
  {k : Type w}
  [Field k]
  {A : Type w}
  [Ring A]
  [Algebra k A]
  {ε : A →ₐ[k] k}
  [CharZero k]
  {a : A}
  {s : Finset ℕ}
  {g : ℕ → k}
  {i : ℕ}
-- given
  (hds : HigherDerivationSystem k A ε)
  (ha : ε a = 0)
  (hne : hds.χ 1 a ≠ 0)
  (hzero : ∑ j ∈ s, g j • a ^ j = 0)
  (hi : i ∈ s) :
-- imply
  g i = 0 := by
-- proof
  suffices key : ∀ n, ∀ j ∈ s, j < n → g j = 0 by
    exact key (i + 1) i hi (Nat.lt_succ_iff.mpr le_rfl)
  intro n
  induction n with
  | zero => intro j _ hjn; omega
  | succ n ih =>
    intro j hj hjn
    by_cases hjn' : j < n
    · exact ih j hj hjn'
    · replace hjn : j = n := by omega
      subst hjn
      have heval : ∑ j' ∈ s, g j' • hds.χ j (a ^ j') = 0 := by
        have := congr_arg (hds.χ j) hzero
        simp only [map_sum, LinearMap.map_smul_of_tower, map_zero] at this; exact this
      rw [← Finset.add_sum_erase s _ hj] at heval
      have : ∑ j' ∈ s.erase j, g j' • hds.χ j (a ^ j') = 0 := by
        apply Finset.sum_eq_zero; intro j' hj'
        have hne' := Finset.ne_of_mem_erase hj'
        have hj'_mem := Finset.mem_of_mem_erase hj'
        by_cases hjlt' : j' < j
        · rw [ih j' hj'_mem hjlt', zero_smul]
        · rw [hds.χ_pow_vanish ha j j' (by omega), smul_zero]
      rw [this, add_zero, hds.χ_pow_diagonal ha, smul_eq_mul] at heval
      exact (mul_eq_zero.mp heval).resolve_right
        (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) (pow_ne_zero _ hne))

end TensorCategories.HigherDerivationSystem

namespace TensorCategories.HigherDerivationSystem

/--
[powers_linearIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
lemma powers_linearIndependent
  {k : Type w}
  [Field k]
  {A : Type w}
  [Ring A]
  [Algebra k A]
  {ε : A →ₐ[k] k}
  [CharZero k]
  {a : A}
-- given
  (hds : HigherDerivationSystem k A ε)
  (ha : ε a = 0)
  (hne : hds.χ 1 a ≠ 0) :
-- imply
  LinearIndependent k (fun n : ℕ => a ^ n) :=
-- proof
  linearIndependent_iff'.mpr fun s g hsum i hi =>
    hds.coeff_zero_of_sum_pow_eq_zero ha hne s g hsum i hi

end TensorCategories.HigherDerivationSystem

/--
[higher_derivation_vanishes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean)
-/
@[path]
private lemma higher_derivation_vanishes_eq
  {k : Type w}
  [Field k]
  {A : Type w}
  [Ring A]
  [Algebra k A]
  {ε : A →ₐ[k] k}
  [CharZero k]
  [FiniteDimensional k A]
-- given
  (hds : HigherDerivationSystem k A ε) :
-- imply
  hds.χ 1 = 0 := by
-- proof
  apply TensorCategories.HigherDerivationSystem.higher_derivation_vanishes hds


-- created on 2026-10-23
