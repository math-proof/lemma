import Lemma.Complex.Eq0AddAddPow_3.of.Eq_Ite_Add_Pow_Inv3.EqSubCeilSSubDivMul3Arg
open Complex


@[main]
private lemma main
  {x a b c : ℂ}
  {k : ℤ}
-- given
  (h₀ : (
    let p : ℂ := b - a ^ 2 / 3
    ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
      (
        let q : ℂ := 2 * a ^ 3 / 27 - a * b / 3 + c
        let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
        let A : ℂ := ((-q + √δ) / 2) ^ (3 : ℂ)⁻¹
        let B : ℂ := ((-q - √δ) / 2) ^ (3 : ℂ)⁻¹
        ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
      )) = k)
  (h₁ : x =
    let p : ℂ := b - a ^ 2 / 3
    let q : ℂ := 2 * a ^ 3 / 27 - a * b / 3 + c
    let ω : ℂ := (I * (2 * π / 3)).exp
    let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
    let A : ℂ := ((-q + √δ) / 2) ^ (3 : ℂ)⁻¹
    let B : ℂ := ((-q - √δ) / 2) ^ (3 : ℂ)⁻¹
    (if k = 0 then A + B else if k % 3 = 1 then A * ω + B else A * ~ω + B) - a / 3):
-- imply
  x ^ 3 + a * x ^ 2 + b * x + c = 0 := by
-- proof
  extract_lets p q δ A B at h₀
  extract_lets ω at h₁
  let z : ℂ :=
    if k = 0 then A + B else if k % 3 = 1 then A * ω + B else A * ~ω + B
  have hz : z ^ 3 + p * z + q = 0 := by
    apply Eq0AddAddPow_3.of.Eq_Ite_Add_Pow_Inv3.EqSubCeilSSubDivMul3Arg.cardano (p := p) (q := q) (x := z) (k := k)
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


-- created on 2018-11-10
-- updated on 2026-08-29
