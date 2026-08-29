import Lemma.Complex.Eq0AddAddPow_3.of.Eq_Ite_Add_Pow_Inv3.EqModSubCeilSSubDivMul3Arg
open Complex


@[main]
private lemma main
  {x a b c : ℂ}
  {d : ℤ}
-- given
  (h₀ : (
    let p : ℂ := b - a ^ 2 / 3
    ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
      (
        let q : ℂ := 2 * a ^ 3 / 27 - a * b / 3 + c
        let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
        let U : ℂ := √δ - q
        let V : ℂ := -√δ - q
        ⌈3 * arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) / (2 * π) - 1 / 2⌉
      )) % 3 = d)
  (h₁ : x =
    let p : ℂ := b - a ^ 2 / 3
    let q : ℂ := 2 * a ^ 3 / 27 - a * b / 3 + c
    let ω : ℂ := ↑(-(1 / 2 : ℝ)) + ↑(√3 / 2 : ℝ) * I
    let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
    let A : ℂ := (√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
    let B : ℂ := (-√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
    (if d = 0 then A + B else if d = 1 then A * ω + B else A * ~ω + B) - a / 3):
-- imply
  x ^ 3 + a * x ^ 2 + b * x + c = 0 := by
-- proof
  extract_lets p q δ U V at h₀
  extract_lets ω A B at h₁
  let z : ℂ :=
    if d = 0 then A + B else if d = 1 then A * ω + B else A * ~ω + B
  have hz : z ^ 3 + p * z + q = 0 := by
    apply Eq0AddAddPow_3.of.Eq_Ite_Add_Pow_Inv3.EqModSubCeilSSubDivMul3Arg (p := p) (q := q) (x := z) (d := d)
    ·
      simpa using h₀
    ·
      extract_lets
      simp [z]
  have hx : x = z - a / 3 := by
    simpa [z] using h₁
  rw [hx]
  simp only [p, q] at hz ⊢
  convert hz using 1
  ring


-- created on 2018-11-20
-- updated on 2026-08-29
