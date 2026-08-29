import Lemma.Complex.AbsCeilSubDivMul3Arg.le.One
import Lemma.Complex.Eq0AddAddPow_3.of.Eq_Ite_Add_Pow_Inv3.EqSubCeilSSubDivMul3Arg
import Lemma.Int.Eq_0.of.Mod_3.eq.Zero.LeAbs_2
open Complex Int


@[main]
private lemma main
  {x p q : ℂ}
  {k : ℤ}
-- given
  (h₀ : (⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
    (
      let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
      let A : ℂ := ((-q + √δ) / 2) ^ (3 : ℂ)⁻¹
      let B : ℂ := ((-q - √δ) / 2) ^ (3 : ℂ)⁻¹
      ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
    )) % 3 = k)
  (h₁ : x =
    let ω : ℂ := (I * (2 * π / 3)).exp
    let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
    let A : ℂ := ((-q + √δ) / 2) ^ (3 : ℂ)⁻¹
    let B : ℂ := ((-q - √δ) / 2) ^ (3 : ℂ)⁻¹
    if k = 0 then A + B else if k = 1 then A * ω + B else A * ~ω + B):
-- imply
  x ^ 3 + p * x + q = 0 := by
-- proof
  let k_alg : ℤ :=
    ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
      (
        let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
        let A : ℂ := ((-q + √δ) / 2) ^ (3 : ℂ)⁻¹
        let B : ℂ := ((-q - √δ) / 2) ^ (3 : ℂ)⁻¹
        ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
      )
  extract_lets δ A B at k_alg
  have hk : k_alg % 3 = k := by
    simpa [k_alg] using h₀
  have hΔ : |k_alg| ≤ 2 := by
    have hp : |⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉| ≤ 1 :=
      AbsCeilSubDivMul3Arg.le.One (-p / 3)
    have hAB :
        |⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉| ≤ 1 :=
      AbsCeilSubDivMul3Arg.le.One _
    simp only [k_alg]
    obtain ⟨hp₁, hp₂⟩ := LeNeg.Le.of.LeAbs hp
    obtain ⟨hAB₁, hAB₂⟩ := LeNeg.Le.of.LeAbs hAB
    apply LeAbs.of.LeNeg.Le
    ·
      omega
    ·
      omega
  apply Eq0AddAddPow_3.of.Eq_Ite_Add_Pow_Inv3.EqSubCeilSSubDivMul3Arg.cardano (k := k_alg)
  ·
    rfl
  ·
    extract_lets ω
    extract_lets at h₁
    rw [h₁]
    if hk0 : k = 0 then
      have hzero : k_alg = 0 :=
        Eq_0.of.Mod_3.eq.Zero.LeAbs_2 hΔ (by
          simpa [hk0] using hk)
      simp [hk0, hzero]
    else if hk1 : k = 1 then
      have hne : k_alg ≠ 0 := by
        intro h
        simp [h] at hk
        omega
      have hmod : k_alg % 3 = 1 := by
        simpa [hk1] using hk
      simp [hk1, hne, hmod]
    else
      have hne : k_alg ≠ 0 := by
        intro h
        simp [h] at hk
        omega
      have hmod : k_alg % 3 ≠ 1 := by
        intro h
        simp [h] at hk
        omega
      simp [hk0, hk1, hne, hmod]


-- created on 2018-11-20
-- updated on 2026-08-29
