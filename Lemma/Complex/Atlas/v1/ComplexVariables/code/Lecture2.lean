import Mathlib
import sympy.Basic
import Def.v1.Atlas.ComplexVariables.code.Lecture2
open Real in Complex


namespace Complex

/--
[exp_add_prop1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture2.lean)
-/
@[path]
lemma exp_add_prop1
  {z w : ℂ} :
-- imply
  exp (z + w) = exp z * exp w :=
-- proof
  exp_add z w

end Complex

/--
[rpow_eq_exp_mul_log](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture2.lean)
-/
@[path]
lemma rpow_eq_exp_mul_log
  {b : ℝ}
  {x : ℝ}
-- given
  (hb : 0 < b) :
-- imply
  b ^ x = Real.exp (x * Real.log b) := by
-- proof
  rw [rpow_def_of_pos hb, mul_comm]

/--
[rpow_add_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture2.lean)
-/
@[path]
lemma rpow_add_mul
  {b : ℝ}
  {x y : ℝ}
-- given
  (hb : 0 < b) :
-- imply
  b ^ (x + y) = b ^ x * b ^ y :=
-- proof
  rpow_add hb x y

/--
[primitiveUnitRoot_isPrimitiveRoot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture2.lean)
-/
@[path]
lemma primitiveUnitRoot_isPrimitiveRoot
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  IsPrimitiveRoot (primitiveUnitRoot n) n :=
-- proof
  Complex.isPrimitiveRoot_exp n hn

/--
[roots_of_unity_eq_powers_of_primitiveUnitRoot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture2.lean)
-/
@[path]
lemma roots_of_unity_eq_powers_of_primitiveUnitRoot
  {n : ℕ}
  {z : ℂ}
-- given
  (hn : 0 < n) :
-- imply
  z ^ n = 1 ↔ ∃ k : Fin n, z = (primitiveUnitRoot n) ^ (k : ℕ) := by
-- proof
  have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  have hprim := primitiveUnitRoot_isPrimitiveRoot n hne
  constructor
  · intro hz
    haveI : NeZero n := ⟨hne⟩
    obtain ⟨i, hi, hiz⟩ := hprim.eq_pow_of_pow_eq_one hz
    exact ⟨⟨i, hi⟩, hiz.symm⟩
  · rintro ⟨k, rfl⟩
    show (primitiveUnitRoot n ^ (k : ℕ)) ^ n = 1
    unfold primitiveUnitRoot
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨(k : ℤ), ?_⟩
    push_cast
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hne
    field_simp

/--
[Complex.log_mul_eq_add_log_add_int](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture2.lean)
-/
@[path]
lemma Complex.log_mul_eq_add_log_add_int
  {z₁ z₂ : ℂ}
-- given
  (hz₁ : z₁ ≠ 0)
  (hz₂ : z₂ ≠ 0) :
-- imply
  ∃ n : ℤ, n ∈ ({-1, 0, 1} : Set ℤ) ∧ Complex.log (z₁ * z₂) = Complex.log z₁ + Complex.log z₂ + ↑n * (2 * ↑π * I) := by
-- proof
  have h1 : exp (log (z₁ * z₂)) = exp (log z₁ + log z₂) := by
    rw [exp_log (mul_ne_zero hz₁ hz₂), Complex.exp_add, exp_log hz₁, exp_log hz₂]
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.mp h1
  refine ⟨n, ?_, hn⟩
  have him_n : arg (z₁ * z₂) = arg z₁ + arg z₂ + n * (2 * π) := by
    have := congr_arg Complex.im hn
    simp [log_im] at this
    linarith
  have hpi : (0 : ℝ) < π := pi_pos
  have hn_bound : -3 * π < n * (2 * π) ∧ n * (2 * π) < 3 * π := by
    constructor <;> nlinarith [neg_pi_lt_arg (z₁ * z₂), arg_le_pi (z₁ * z₂),
      neg_pi_lt_arg z₁, neg_pi_lt_arg z₂, arg_le_pi z₁, arg_le_pi z₂]
  have hn_le : n ≤ 1 := by
    by_contra h
    push Not at h
    have : (2 : ℝ) ≤ n := by exact_mod_cast h
    nlinarith
  have hn_ge : -1 ≤ n := by
    by_contra h
    push Not at h
    have : n ≤ -2 := by omega
    have : (n : ℝ) ≤ -2 := by exact_mod_cast this
    nlinarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega


-- created on 2026-10-23
