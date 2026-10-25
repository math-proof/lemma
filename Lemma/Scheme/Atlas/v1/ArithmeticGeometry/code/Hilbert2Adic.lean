import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.Hilbert2Adic
open Polynomial PadicInt HilbertSymbol


/--
[PadicInt.toZModPow_surjective'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2Adic.lean)
-/
@[path]
lemma PadicInt.toZModPow_surjective'
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {n : ℕ} :
-- imply
  Function.Surjective (toZModPow n : ℤ_[p] →+* ZMod (p ^ n)) := by
-- proof
  intro x
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective x
  exact ⟨k, by rw [map_intCast, hk]⟩

/--
[PadicInt.toZModPow_eq_zero_iff_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2Adic.lean)
-/
@[path]
lemma PadicInt.toZModPow_eq_zero_iff_dvd
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {n : ℕ}
  {x : ℤ_[p]} :
-- imply
  toZModPow n x = 0 ↔ (p : ℤ_[p]) ^ n ∣ x := by
-- proof
  rw [← RingHom.mem_ker, ker_toZModPow, Ideal.mem_span_singleton]

/--
[norm_two_padic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2Adic.lean)
-/
@[path]
lemma norm_two_padic
-- imply
  ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by
-- proof
  rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) from rfl]
  exact_mod_cast @PadicInt.norm_p 2 (Fact.mk Nat.prime_two)

/--
[exists_mul_sq_eq_of_mod8](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2Adic.lean)
-/
@[path]
lemma exists_mul_sq_eq_of_mod8
  {a c z : ℤ_[2]}
-- given
  (ha : IsUnit a)
  (hz : IsUnit z)
  (hdvd : (2 : ℤ_[2]) ^ 3 ∣ a * z ^ 2 - c) :
-- imply
  ∃ z' : ℤ_[2], a * z' ^ 2 = c ∧ IsUnit z' := by
-- proof
  let f : Polynomial ℤ_[2] := C a * X ^ 2 - C c
  have ha_norm : ‖(a : ℤ_[2])‖ = 1 := PadicInt.isUnit_iff.mp ha
  have hz_norm : ‖(z : ℤ_[2])‖ = 1 := PadicInt.isUnit_iff.mp hz
  have hf_aeval : Polynomial.aeval z f = a * z ^ 2 - c := by
    simp [f, aeval_def, eval₂_eq_eval_map]
  have hf_deriv_aeval : Polynomial.aeval z f.derivative = 2 * a * z := by
    simp [f, derivative_sub, derivative_mul, derivative_C, derivative_pow, derivative_X,
      aeval_def, eval₂_eq_eval_map]; ring
  have hnorm_f : ‖Polynomial.aeval z f‖ ≤ ‖(2 : ℤ_[2])‖ ^ 3 := by
    rw [hf_aeval]
    obtain ⟨c', hc'⟩ := hdvd
    rw [hc', norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one c')
  have hensel_cond : ‖Polynomial.aeval z f‖ < ‖Polynomial.aeval z f.derivative‖ ^ 2 := by
    rw [hf_deriv_aeval, norm_mul, norm_mul, norm_two_padic, ha_norm, hz_norm]
    calc ‖Polynomial.aeval z f‖ ≤ ‖(2 : ℤ_[2])‖ ^ 3 := hnorm_f
      _ = ((2 : ℝ)⁻¹) ^ 3 := by rw [norm_two_padic]
      _ < ((2 : ℝ)⁻¹ * 1 * 1) ^ 2 := by norm_num
  obtain ⟨z', hz'_root, hz'_close, _, _⟩ := hensels_lemma hensel_cond
  have hz'_unit : IsUnit z' := by
    rw [PadicInt.isUnit_iff]
    have hsub : ‖z' - z‖ < ‖z‖ := by
      calc ‖z' - z‖ < ‖Polynomial.aeval z f.derivative‖ := hz'_close
        _ = ‖2 * a * z‖ := by rw [hf_deriv_aeval]
        _ = ‖(2 : ℤ_[2])‖ * ‖a‖ * ‖z‖ := by rw [norm_mul, norm_mul]
        _ = (2 : ℝ)⁻¹ * 1 * 1 := by rw [norm_two_padic, ha_norm, hz_norm]
        _ < 1 := by norm_num
        _ = ‖z‖ := hz_norm.symm
    have : ‖z'‖ = ‖z‖ := by
      simp only [PadicInt.norm_def] at *
      exact Padic.norm_eq_of_norm_sub_lt_right (by exact_mod_cast hsub)
    rw [this, hz_norm]
  have heq' : a * z' ^ 2 = c := by
    simp [f, aeval_def, eval₂_eq_eval_map] at hz'_root
    exact sub_eq_zero.mp hz'_root
  exact ⟨z', heq', hz'_unit⟩

/--
[padicUnit_one_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2Adic.lean)
-/
@[path]
lemma padicUnit_one_val
  {u : ℤ_[2]ˣ} :
-- imply
  (padicUnit_one u : ℚ_[2]) = ((↑u : ℤ_[2]) : ℚ_[2]) :=
-- proof
  IsUnit.unit_spec _

/--
[padicUnit_two_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2Adic.lean)
-/
@[path]
lemma padicUnit_two_val
  {u : ℤ_[2]ˣ} :
-- imply
  (padicUnit_two u : ℚ_[2]) = 2 * ((↑u : ℤ_[2]) : ℚ_[2]) :=
-- proof
  IsUnit.unit_spec _

/--
[lift_eq_to_Qp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2Adic.lean)
-/
@[path]
lemma lift_eq_to_Qp
  {a b : ℤ_[2]}
-- given
  (h : a = b) :
-- imply
  (a : ℚ_[2]) = (b : ℚ_[2]) :=
-- proof
  congr_arg Subtype.val h

/--
[lemma_10_8_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2Adic.lean)
-/
@[path]
lemma lemma_10_8_one
  {u v : ℤ_[2]ˣ} :
-- imply
  HasPrimitiveSolution (padicUnit_one u) (padicUnit_one v) ↔ HasPrimitiveSolutionMod8_one u v := by
-- proof
  constructor
  ·
    intro ⟨x, y, z, hprim, heq⟩
    have heq_Z2 : (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2 = z ^ 2 := by
      rw [padicUnit_one_val, padicUnit_one_val] at heq
      apply Subtype.val_injective
      have h := lift_eq_to_Qp (a := (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2) (b := z ^ 2) ?_
      · exact h
      · apply Subtype.val_injective
        push_cast
        exact heq
    refine ⟨toZModPow 3 x, toZModPow 3 y, toZModPow 3 z, ?_, ?_⟩
    · rcases hprim with hx | hy | hz
      · exact Or.inl (hx.map (toZModPow 3))
      · exact Or.inr (Or.inl (hy.map (toZModPow 3)))
      · exact Or.inr (Or.inr (hz.map (toZModPow 3)))
    · have := congr_arg (toZModPow 3) heq_Z2
      simp only [map_add, map_mul, map_pow] at this; exact this.symm
  ·
    intro ⟨x₀, y₀, z₀, hprim, heq⟩
    obtain ⟨x, hx⟩ := PadicInt.toZModPow_surjective' 3 x₀
    obtain ⟨y, hy⟩ := PadicInt.toZModPow_surjective' 3 y₀
    obtain ⟨z, hz⟩ := PadicInt.toZModPow_surjective' 3 z₀
    have heq_mod : toZModPow 3 (z ^ 2 - ((↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2)) = 0 := by
      simp only [map_sub, map_add, map_mul, map_pow, hx, hy, hz]
      rw [sub_eq_zero]; exact heq
    have hdvd : (2 : ℤ_[2]) ^ 3 ∣ z ^ 2 - ((↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2) :=
      (PadicInt.toZModPow_eq_zero_iff_dvd _ _).mp heq_mod
    obtain hx_unit | hy_unit | hz_unit := hprim
    ·
      have hxu : IsUnit x := by
        have := (hx ▸ hx_unit : IsUnit (toZModPow 3 x))
        rwa [PadicInt.isUnit_toZModPow_iff (by norm_num : (0 : ℕ) < 3)] at this
      have hdvd' : (2 : ℤ_[2]) ^ 3 ∣ (↑u : ℤ_[2]) * x ^ 2 - (z ^ 2 - (↑v : ℤ_[2]) * y ^ 2) := by
        have : (↑u : ℤ_[2]) * x ^ 2 - (z ^ 2 - (↑v : ℤ_[2]) * y ^ 2) =
          -(z ^ 2 - ((↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2)) := by ring
        rw [this]; exact dvd_neg.mpr hdvd
      obtain ⟨x', hx'_eq, hx'_unit⟩ :=
        exists_mul_sq_eq_of_mod8 (Units.isUnit u) hxu hdvd'
      have heq_final : (↑u : ℤ_[2]) * x' ^ 2 + (↑v : ℤ_[2]) * y ^ 2 = z ^ 2 := by
        linear_combination hx'_eq
      refine ⟨x', y, z, Or.inl hx'_unit, ?_⟩
      rw [padicUnit_one_val, padicUnit_one_val]
      have h := congr_arg (Subtype.val : ℤ_[2] → ℚ_[2]) heq_final
      push_cast at h ⊢
      exact h
    ·
      have hyu : IsUnit y := by
        have := (hy ▸ hy_unit : IsUnit (toZModPow 3 y))
        rwa [PadicInt.isUnit_toZModPow_iff (by norm_num : (0 : ℕ) < 3)] at this
      have hdvd' : (2 : ℤ_[2]) ^ 3 ∣ (↑v : ℤ_[2]) * y ^ 2 - (z ^ 2 - (↑u : ℤ_[2]) * x ^ 2) := by
        have : (↑v : ℤ_[2]) * y ^ 2 - (z ^ 2 - (↑u : ℤ_[2]) * x ^ 2) =
          -(z ^ 2 - ((↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2)) := by ring
        rw [this]; exact dvd_neg.mpr hdvd
      obtain ⟨y', hy'_eq, hy'_unit⟩ :=
        exists_mul_sq_eq_of_mod8 (Units.isUnit v) hyu hdvd'
      have heq_final : (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y' ^ 2 = z ^ 2 := by
        linear_combination hy'_eq
      refine ⟨x, y', z, Or.inr (Or.inl hy'_unit), ?_⟩
      rw [padicUnit_one_val, padicUnit_one_val]
      have h := congr_arg (Subtype.val : ℤ_[2] → ℚ_[2]) heq_final
      push_cast at h ⊢
      exact h
    ·
      have hzu : IsUnit z := by
        have := (hz ▸ hz_unit : IsUnit (toZModPow 3 z))
        rwa [PadicInt.isUnit_toZModPow_iff (by norm_num : (0 : ℕ) < 3)] at this
      have hdvd1 : (2 : ℤ_[2]) ^ 3 ∣ 1 * z ^ 2 - ((↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2) := by
        rw [one_mul]; exact hdvd
      obtain ⟨z', hz'_eq, hz'_unit⟩ :=
        exists_mul_sq_eq_of_mod8 isUnit_one hzu hdvd1
      have heq_final : (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2 = z' ^ 2 := by
        rw [one_mul] at hz'_eq; linear_combination -hz'_eq
      refine ⟨x, y, z', Or.inr (Or.inr hz'_unit), ?_⟩
      rw [padicUnit_one_val, padicUnit_one_val]
      have h := congr_arg (Subtype.val : ℤ_[2] → ℚ_[2]) heq_final
      push_cast at h ⊢
      exact h

/--
[no_prim_sol_two_x_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2Adic.lean)
-/
@[path]
lemma no_prim_sol_two_x_unit
-- imply
  ∀ (u₀ v₀ : (ZMod (2 ^ 3))ˣ) (x₀ y₀ z₀ : ZMod (2 ^ 3)), IsUnit x₀ → ¬IsUnit y₀ → ¬IsUnit z₀ → z₀ ^ 2 = 2 * (↑u₀ : ZMod (2 ^ 3)) * x₀ ^ 2 + (↑v₀ : ZMod (2 ^ 3)) * y₀ ^ 2 → False := by
-- proof
decide

/--
[lemma_10_8_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2Adic.lean)
-/
@[path]
lemma lemma_10_8_two
  {u v : ℤ_[2]ˣ} :
-- imply
  HasPrimitiveSolution (padicUnit_two u) (padicUnit_one v) ↔ HasPrimitiveSolutionMod8_two u v := by
-- proof
  constructor
  ·
    intro ⟨x, y, z, hprim, heq⟩
    have heq_Z2 : 2 * (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2 = z ^ 2 := by
      rw [padicUnit_two_val, padicUnit_one_val] at heq
      suffices h : ((2 * (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2 : ℤ_[2]) : ℚ_[2]) =
        ((z ^ 2 : ℤ_[2]) : ℚ_[2]) from Subtype.val_injective h
      push_cast; norm_cast
    refine ⟨toZModPow 3 x, toZModPow 3 y, toZModPow 3 z, ?_, ?_⟩
    · rcases hprim with hx | hy | hz
      · exact Or.inl (hx.map (toZModPow 3))
      · exact Or.inr (Or.inl (hy.map (toZModPow 3)))
      · exact Or.inr (Or.inr (hz.map (toZModPow 3)))
    · have := congr_arg (toZModPow 3) heq_Z2
      simp only [map_add, map_mul, map_pow, map_ofNat] at this
      exact this.symm
  ·
    intro ⟨x₀, y₀, z₀, hprim, heq⟩
    obtain ⟨x, hx⟩ := PadicInt.toZModPow_surjective' 3 x₀
    obtain ⟨y, hy⟩ := PadicInt.toZModPow_surjective' 3 y₀
    obtain ⟨z, hz⟩ := PadicInt.toZModPow_surjective' 3 z₀
    have heq_mod : toZModPow 3 (z ^ 2 - (2 * (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2)) = 0 := by
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, hx, hy, hz]
      rw [sub_eq_zero]; linear_combination heq
    have hdvd : (2 : ℤ_[2]) ^ 3 ∣ z ^ 2 - (2 * (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2) :=
      (PadicInt.toZModPow_eq_zero_iff_dvd _ _).mp heq_mod
    have hyz_unit : IsUnit y₀ ∨ IsUnit z₀ := by
      obtain hx_unit | hy | hz := hprim
      · by_contra h
        push Not at h
        obtain ⟨hny, hnz⟩ := h
        have hu₀ : IsUnit (toZModPow 3 (↑u : ℤ_[2])) := (Units.isUnit u).map _
        have hv₀ : IsUnit (toZModPow 3 (↑v : ℤ_[2])) := (Units.isUnit v).map _
        exact no_prim_sol_two_x_unit hu₀.unit hv₀.unit x₀ y₀ z₀ hx_unit hny hnz
          (by simp only [IsUnit.unit_spec]; exact heq)
      · exact Or.inl hy
      · exact Or.inr hz
    obtain hy_unit | hz_unit := hyz_unit
    ·
      have hyu : IsUnit y := by
        have := (hy ▸ hy_unit : IsUnit (toZModPow 3 y))
        rwa [PadicInt.isUnit_toZModPow_iff (by norm_num : (0 : ℕ) < 3)] at this
      have hdvd' : (2 : ℤ_[2]) ^ 3 ∣
        (↑v : ℤ_[2]) * y ^ 2 - (z ^ 2 - 2 * (↑u : ℤ_[2]) * x ^ 2) := by
        have : (↑v : ℤ_[2]) * y ^ 2 - (z ^ 2 - 2 * (↑u : ℤ_[2]) * x ^ 2) =
          -(z ^ 2 - (2 * (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2)) := by ring
        rw [this]; exact dvd_neg.mpr hdvd
      obtain ⟨y', hy'_eq, hy'_unit⟩ :=
        exists_mul_sq_eq_of_mod8 (Units.isUnit v) hyu hdvd'
      have heq_final : 2 * (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y' ^ 2 = z ^ 2 := by
        linear_combination hy'_eq
      refine ⟨x, y', z, Or.inr (Or.inl hy'_unit), ?_⟩
      rw [padicUnit_two_val, padicUnit_one_val]
      have h := congr_arg (Subtype.val : ℤ_[2] → ℚ_[2]) heq_final
      push_cast at h ⊢; norm_cast
    ·
      have hzu : IsUnit z := by
        have := (hz ▸ hz_unit : IsUnit (toZModPow 3 z))
        rwa [PadicInt.isUnit_toZModPow_iff (by norm_num : (0 : ℕ) < 3)] at this
      have hdvd1 : (2 : ℤ_[2]) ^ 3 ∣
        1 * z ^ 2 - (2 * (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2) := by
        rw [one_mul]; exact hdvd
      obtain ⟨z', hz'_eq, hz'_unit⟩ :=
        exists_mul_sq_eq_of_mod8 isUnit_one hzu hdvd1
      have heq_final : 2 * (↑u : ℤ_[2]) * x ^ 2 + (↑v : ℤ_[2]) * y ^ 2 = z' ^ 2 := by
        rw [one_mul] at hz'_eq; linear_combination -hz'_eq
      refine ⟨x, y, z', Or.inr (Or.inr hz'_unit), ?_⟩
      rw [padicUnit_two_val, padicUnit_one_val]
      have h := congr_arg (Subtype.val : ℤ_[2] → ℚ_[2]) heq_final
      push_cast at h ⊢; norm_cast

/--
[PadicInt.isUnit_toZModPow_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2Adic.lean)
-/
@[path]
private lemma isUnit_toZModPow_iff_eq
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {n : ℕ}
  {x : ℤ_[p]}
-- given
  (hn : 0 < n) :
-- imply
  IsUnit (toZModPow n x) ↔ IsUnit x := by
-- proof
  apply PadicInt.isUnit_toZModPow_iff hn


-- created on 2026-10-23
