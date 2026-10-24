import Mathlib
import Lemma.AdicCompletion.IsCompact.LocalLevelOne

open IsDedekindDomain NumberField Matrix
attribute [-ext] IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext

/-! FLT AdelicDock shared defs/lemmas (not a rendered path lemma). -/

namespace AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem isOpen_setOf_valued_le (t : v.adicCompletion K) (ht : t ≠ 0) :
    IsOpen {y : v.adicCompletion K | Valued.v y ≤ Valued.v t} := by
  rw [setOf_valued_le_eq_preimage v t ht]
  exact (continuous_id.mul continuous_const).isOpen_preimage _
    (Valued.isOpen_valuationSubring _)

theorem isOpen_setOf_valued_le_idealBound {N : Ideal R} (hN : N ≠ ⊥) :
    IsOpen {y : v.adicCompletion K | Valued.v y ≤ idealBound R N v} := by
  obtain ⟨t, ht, hvt⟩ := exists_valued_eq_exp_neg (K := K) v
    ((Associates.mk v.asIdeal).count (Associates.mk N).factors)
  rw [idealBound_of_ne_bot hN, ← hvt]
  exact isOpen_setOf_valued_le R K v t ht

end AdelicLevel

namespace AdelicLevel

theorem idealBound_pow (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (m : ℕ) : idealBound (𝓞 F) (v.asIdeal ^ m) v = WithZero.exp (-(m : ℤ)) := by
  classical
  have hN : v.asIdeal ^ m ≠ ⊥ := pow_ne_zero _ v.ne_bot
  rw [idealBound_of_ne_bot hN, Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr v.ne_bot)
      (Associates.irreducible_mk.mpr v.irreducible),
    Associates.count_self (Associates.irreducible_mk.mpr v.irreducible)]
  simp

end AdelicLevel

noncomputable def unipotent
    (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (y : v.adicCompletion F) : GL (Fin 2) (v.adicCompletion F) :=
  GeneralLinearGroup.mkOfDetNeZero !![1, y; 0, 1] (by simp [det_fin_two_of])

noncomputable def diagZ
    (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletion F) (hπ : ϖ ≠ 0) (n : ℤ) : GL (Fin 2) (v.adicCompletion F) :=
  GeneralLinearGroup.mkOfDetNeZero !![ϖ ^ n, 0; 0, 1]
    (by simp [det_fin_two_of, zpow_ne_zero n hπ])

namespace K1Struct

open AdelicDock

variable {F : Type*} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

local notation "Kv" => (HeightOneSpectrum.adicCompletion F v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion F v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion F v))

theorem coe_unipotent (y : Kv) : ((unipotent F v y : G) : Mat) = !![1, y; 0, 1] := rfl

theorem coe_diagZ (ϖ : Kv) (hπ : ϖ ≠ 0) (n : ℤ) : ((diagZ F v ϖ hπ n : G) : Mat) = !![ϖ ^ n, 0; 0, 1] := rfl

theorem v_zpow_uniformizer {ϖ : Kv} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (n : ℤ) :
    Valued.v (ϖ ^ n) = WithZero.exp (-n) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem mem_integers_iff (x : Kv) : x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 :=
  HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v

theorem idealBound_pow (m : ℕ) : AdelicLevel.idealBound (𝓞 F) (v.asIdeal ^ m) v = WithZero.exp (-(m : ℤ)) := by
  classical
  have hN : v.asIdeal ^ m ≠ ⊥ := pow_ne_zero _ v.ne_bot
  rw [AdelicLevel.idealBound_of_ne_bot hN, Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr v.ne_bot) (Associates.irreducible_mk.mpr v.irreducible),
    Associates.count_self (Associates.irreducible_mk.mpr v.irreducible)]
  simp

theorem structure_lemma (ϖ : v.adicCompletionIntegers F) (hπ : (ϖ : Kv) ≠ 0)
    (hϖ : Valued.v (ϖ : Kv) = WithZero.exp (-1 : ℤ)) (m : ℕ)
    (hB : AdelicLevel.idealBound (𝓞 F) (v.asIdeal ^ m) v < 1) (g : G)
    (hc : Valued.v ((g : Mat) 1 0) ≤ AdelicLevel.idealBound (𝓞 F) (v.asIdeal ^ m) v)
    (hd : Valued.v ((g : Mat) 1 1 - 1) ≤ AdelicLevel.idealBound (𝓞 F) (v.asIdeal ^ m) v) :
    ∃ (x : Kv) (n : ℤ) (k : G), k ∈ localLevelOne (𝓞 F) F v (v.asIdeal ^ m) ∧
      g = unipotent F v x * diagZ F v (ϖ : Kv) hπ n * k ∧ Valued.v ((g : Mat).det) = WithZero.exp (-n) := by
  set B := AdelicLevel.idealBound (𝓞 F) (v.asIdeal ^ m) v with hBdef
  set a : Kv := (g : Mat) 0 0 with ha
  set b : Kv := (g : Mat) 0 1 with hb
  set c : Kv := (g : Mat) 1 0 with hcdef
  set d : Kv := (g : Mat) 1 1 with hddef
  have hc' : Valued.v c ≤ B := hc
  have hd' : Valued.v (d - 1) ≤ B := hd
  have hd1 : Valued.v d = 1 := by
    have := Valuation.map_one_add_of_lt Valued.v (lt_of_le_of_lt hd' hB)
    rwa [add_sub_cancel] at this
  have hd0 : d ≠ 0 := fun h => by rw [h, map_zero] at hd1; exact zero_ne_one hd1
  have hD : (g : Mat).det = a * d - b * c := by rw [Matrix.det_fin_two]
  have hD0 : (g : Mat).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det g).ne_zero
  set y : Kv := (g : Mat).det / d with hy
  have hy0 : y ≠ 0 := div_ne_zero hD0 hd0
  have hvy0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
  set n : ℤ := -(Valued.v y).log with hn
  have hvy : Valued.v y = WithZero.exp (-n) := by rw [hn, neg_neg, WithZero.exp_log hvy0]
  have hϖn : Valued.v ((ϖ : Kv) ^ n) = WithZero.exp (-n) := v_zpow_uniformizer hϖ n
  have hϖn0 : (ϖ : Kv) ^ n ≠ 0 := zpow_ne_zero n hπ
  set u : Kv := y / (ϖ : Kv) ^ n with hu
  have hvu : Valued.v u = 1 := by rw [hu, map_div₀, hvy, hϖn, div_self WithZero.exp_ne_zero]
  have hu0 : u ≠ 0 := fun h => by rw [h, map_zero] at hvu; exact zero_ne_one hvu
  have hB1 : B ≤ 1 := hB.le

  have hdetk : (!![u, 0; c, d] : Mat).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]; simp [hu0, hd0]
  refine ⟨b / d, n, Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetk, ?_, ?_, ?_⟩
  ·
    rw [mem_localLevelOne_iff]
    have hinvdet : (!![u⁻¹, 0; -(c / (u * d)), d⁻¹] : Mat).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]; simp [hu0, hd0]
    have hinv : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetk : G)⁻¹ =
        Matrix.GeneralLinearGroup.mkOfDetNeZero _ hinvdet := by
      apply inv_eq_of_mul_eq_one_right
      apply Units.ext
      simp only [Units.val_mul, Units.val_one, Matrix.GeneralLinearGroup.mkOfDetNeZero]
      ext i j
      fin_cases i <;> fin_cases j
      all_goals
        simp [Matrix.mul_apply, Fin.sum_univ_two]
        try field_simp
        try ring
    constructor
    · refine ⟨fun i j => ?_, ?_, ?_⟩
      · fin_cases i <;> fin_cases j <;>
          simp only [Matrix.GeneralLinearGroup.mkOfDetNeZero, mem_integers_iff]
        · exact hvu.le
        · simp
        · exact hc'.trans hB1
        · exact hd1.le
      · simpa [Matrix.GeneralLinearGroup.mkOfDetNeZero] using hc'
      · simpa [Matrix.GeneralLinearGroup.mkOfDetNeZero] using hd'
    · rw [hinv]
      refine ⟨fun i j => ?_, ?_, ?_⟩
      · fin_cases i <;> fin_cases j <;> rw [mem_integers_iff]
        · show Valued.v u⁻¹ ≤ 1
          rw [map_inv₀, hvu, inv_one]
        · show Valued.v (0 : Kv) ≤ 1
          simp
        · show Valued.v (-(c / (u * d))) ≤ 1
          rw [Valuation.map_neg, map_div₀, map_mul, hvu, hd1, one_mul, div_one]; exact hc'.trans hB1
        · show Valued.v d⁻¹ ≤ 1
          rw [map_inv₀, hd1, inv_one]
      · show Valued.v (-(c / (u * d))) ≤ B
        rw [Valuation.map_neg, map_div₀, map_mul, hvu, hd1, one_mul, div_one]; exact hc'
      · show Valued.v (d⁻¹ - 1) ≤ B
        have : d⁻¹ - 1 = -((d - 1) / d) := by field_simp; ring
        rw [this, Valuation.map_neg, map_div₀, hd1, div_one]; exact hd'
  ·
    apply Units.ext
    simp only [Units.val_mul, coe_unipotent, coe_diagZ, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    ext i j
    fin_cases i <;> fin_cases j
    · show a = _
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [hu, hy, hD]; field_simp; ring
    · show b = _
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
    · show c = _
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    · show d = _
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  ·
    have : (g : Mat).det = y * d := by rw [hy]; field_simp
    rw [this, map_mul, hvy, hd1, mul_one]

end K1Struct

theorem structure_lemma
    (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletionIntegers F) (hπ : (ϖ : v.adicCompletion F) ≠ 0)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) (m : ℕ)
    (hB : AdelicLevel.idealBound (𝓞 F) (v.asIdeal ^ m) v < 1)
    (g : GL (Fin 2) (v.adicCompletion F))
    (hc : Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0)
      ≤ AdelicLevel.idealBound (𝓞 F) (v.asIdeal ^ m) v)
    (hd : Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 - 1)
      ≤ AdelicLevel.idealBound (𝓞 F) (v.asIdeal ^ m) v) : Nonempty
    (Σ' (x : v.adicCompletion F) (n : ℤ) (k : GL (Fin 2) (v.adicCompletion F)),
      k ∈ AdelicDock.localLevelOne (𝓞 F) F v (v.asIdeal ^ m) ∧
      g = unipotent F v x * diagZ F v (ϖ : v.adicCompletion F) hπ n * k ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det) = WithZero.exp (-n)) := by
  obtain ⟨x, n, k, hk, hg, hv⟩ :=
    K1Struct.structure_lemma (F := F) (v := v) ϖ hπ hϖ m hB g hc hd
  exact ⟨⟨x, n, k, hk, hg, hv⟩⟩
