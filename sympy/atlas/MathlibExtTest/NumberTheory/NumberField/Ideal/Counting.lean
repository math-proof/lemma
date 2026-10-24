/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Ideal/Counting.lean -/


import sympy.atlas.NumberTheory.NumberField.Ideal.Counting
import Lemma.Ideal.NumberField.Ideal.Counting
import Mathlib.Tactic.NormNum

open scoped NumberField

-- Generic signature of the integer-threshold bound.
example (K : Type*) [Field K] [NumberField K] (M : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} ≤
      (Module.finrank ℚ K * M) ^ Nat.log 2 M :=
  NumberField.Ideal.card_nonzero_absNorm_le K M

-- The `M = 0` edge case: no nonzero ideal has norm `≤ 0`.
example (K : Type*) [Field K] [NumberField K] :
    Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ 0} = 0 := by
  let _ : Fintype {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ 0} :=
    Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
  exact ⟨fun ⟨I, hne, hle⟩ =>
    hne (Ideal.absNorm_eq_zero_iff.mp (Nat.le_zero.mp hle))⟩

-- The `M = 1` edge case: only the top ideal has norm `≤ 1`.
example (K : Type*) [Field K] [NumberField K] :
    Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ 1} = 1 := by
  let _ : Fintype {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ 1} :=
    Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
  have htop1 : Ideal.absNorm (⊤ : Ideal (𝓞 K)) = 1 :=
    Ideal.absNorm_eq_one_iff.mpr rfl
  have htop_ne : (⊤ : Ideal (𝓞 K)) ≠ ⊥ := by
    intro h
    have h0 : Ideal.absNorm (⊤ : Ideal (𝓞 K)) = 0 :=
      Ideal.absNorm_eq_zero_iff.mpr h
    rw [htop1] at h0
    exact absurd h0 (by norm_num)
  refine ⟨⟨⊤, htop_ne, htop1.le⟩, fun b => ?_⟩
  obtain ⟨I, hne, hle⟩ := b
  have hne0 : Ideal.absNorm I ≠ 0 :=
    fun h0 => hne (Ideal.absNorm_eq_zero_iff.mp h0)
  have h1 : Ideal.absNorm I = 1 := by omega
  have hI : I = ⊤ := Ideal.absNorm_eq_one_iff.mp h1
  exact Subtype.ext hI

-- Specialization to `K = ℚ`.
example :
    Nat.card {I : Ideal (𝓞 ℚ) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ 10} ≤
      (Module.finrank ℚ ℚ * 10) ^ Nat.log 2 10 :=
  NumberField.Ideal.card_nonzero_absNorm_le ℚ 10

-- The bounded subtype is genuinely finite, so `Nat.card` is nonvacuous.
example (K : Type*) [Field K] [NumberField K] (M : ℕ) :
    Finite {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} :=
  inferInstance

-- Real threshold at `M = 1`.
example (K : Type*) [Field K] [NumberField K] :
    Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ 1} ≤
      (Module.finrank ℚ K * ⌊(1 : ℝ)⌋₊) ^ Nat.log 2 ⌊(1 : ℝ)⌋₊ :=
  NumberField.Ideal.card_nonzero_absNorm_le_real K 1

-- Real nonintegral threshold `M = 3 / 2`.
example (K : Type*) [Field K] [NumberField K] :
    Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ 3 / 2} ≤
      (Module.finrank ℚ K * ⌊(3 : ℝ) / 2⌋₊) ^ Nat.log 2 ⌊(3 : ℝ) / 2⌋₊ :=
  NumberField.Ideal.card_nonzero_absNorm_le_real K (3 / 2)

-- Exact textbook endpoint with real `rpow`, generic positive `M`.
example (K : Type*) [Field K] [NumberField K] (M : ℝ) (hM : 0 < M) :
    (Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} : ℝ) ≤
      ((Module.finrank ℚ K : ℝ) * M) ^ (Real.logb 2 M) :=
  NumberField.Ideal.card_nonzero_absNorm_le_real_rpow K M hM

-- Exact endpoint at `M = 1 / 2`: the empty branch (`M < 1`).
example (K : Type*) [Field K] [NumberField K] :
    (Nat.card {I : Ideal (𝓞 K) //
      I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ 1 / 2} : ℝ) ≤
      ((Module.finrank ℚ K : ℝ) * (1 / 2)) ^ (Real.logb 2 (1 / 2)) :=
  NumberField.Ideal.card_nonzero_absNorm_le_real_rpow K _ (by norm_num)

-- Exact endpoint at `M = 1`.
example (K : Type*) [Field K] [NumberField K] :
    (Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ 1} : ℝ) ≤
      ((Module.finrank ℚ K : ℝ) * 1) ^ (Real.logb 2 1) :=
  NumberField.Ideal.card_nonzero_absNorm_le_real_rpow K _ (by norm_num)

-- Exact endpoint at nonintegral `M = 3 / 2`.
example (K : Type*) [Field K] [NumberField K] :
    (Nat.card {I : Ideal (𝓞 K) //
      I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ 3 / 2} : ℝ) ≤
      ((Module.finrank ℚ K : ℝ) * (3 / 2)) ^ (Real.logb 2 (3 / 2)) :=
  NumberField.Ideal.card_nonzero_absNorm_le_real_rpow K _ (by norm_num)
