import Lemma.Complex.AbsCeilSubDivMul3Arg.le.One
import Lemma.Complex.Eq0AddAddPow_3.of.Eq_Ite_Add_Pow_Inv3.EqSubCeilSSubDivMul3Arg
import Lemma.Int.Eq_0.of.Mod_3.eq.Zero.LeAbs_2
open Complex Int


@[main]
private lemma main
  {x p q : ℂ}
  {d : ℤ}
-- given
  (h₀ : (⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
    (
      let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
      let A : ℂ := (√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
      let B : ℂ := (-√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
      ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
    )) % 3 = d)
  (h₁ : x =
    let ω : ℂ := (I * (2 * π / 3)).exp
    let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
    let A : ℂ := (√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
    let B : ℂ := (-√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
    if d = 0 then A + B else if d = 1 then A * ω + B else A * ~ω + B):
-- imply
  x ^ 3 + p * x + q = 0 := by
-- proof
  let d_alg : ℤ :=
    ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
      (
        let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
        let A : ℂ := (√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
        let B : ℂ := (-√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
        ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
      )
  extract_lets δ A B at d_alg
  have hd : d_alg % 3 = d := by
    simpa [d_alg] using h₀
  have hΔ : |d_alg| ≤ 2 := by
    have hp : |⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉| ≤ 1 :=
      AbsCeilSubDivMul3Arg.le.One (-p / 3)
    have hAB :
        |⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉| ≤ 1 :=
      AbsCeilSubDivMul3Arg.le.One _
    simp only [d_alg]
    obtain ⟨hp₁, hp₂⟩ := LeNeg.Le.of.LeAbs hp
    obtain ⟨hAB₁, hAB₂⟩ := LeNeg.Le.of.LeAbs hAB
    apply LeAbs.of.LeNeg.Le
    ·
      omega
    ·
      omega
  apply Eq0AddAddPow_3.of.Eq_Ite_Add_Pow_Inv3.EqSubCeilSSubDivMul3Arg.cardano (d := d_alg)
  ·
    rfl
  ·
    extract_lets ω
    extract_lets at h₁
    rw [h₁]
    if hd0 : d = 0 then
      have hzero : d_alg = 0 :=
        Eq_0.of.Mod_3.eq.Zero.LeAbs_2 hΔ (by
          simpa [hd0] using hd)
      simp [hd0, hzero]
    else if hd1 : d = 1 then
      have hne : d_alg ≠ 0 := by
        intro h
        simp [h] at hd
        omega
      have hmod : d_alg % 3 = 1 := by
        simpa [hd1] using hd
      simp [hd1, hne, hmod]
    else
      have hne : d_alg ≠ 0 := by
        intro h
        simp [h] at hd
        omega
      have hmod : d_alg % 3 ≠ 1 := by
        intro h
        simp [h] at hd
        omega
      simp [hd0, hd1, hne, hmod]


-- created on 2018-11-20
-- updated on 2026-08-29
