import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Theorem.Function
open Polynomial
set_option maxHeartbeats 800000


/--
Closed form of the order-4 homogeneous recurrence
`h[k + 4] = c₀ * h[k] + c₁ * h[k + 1] + c₂ * h[k + 2] + c₃ * h[k + 3]`
over `ℂ`. `Nat.descFactorial` is the falling product `n (n - 1) ⋯ (n - e + 1)`,
so a root of multiplicity `m` contributes the powers `e = 0, …, m - 1`, and a
quadruple root `0` still frees `h[3]`.
-/
@[path]
private lemma main
  {h : ℕ ⇀ ℂ}
  {c₀ c₁ c₂ c₃ : ℂ}
-- given
  (hrec : ∀ k : ℕ,
    h[k + 4] = c₀ * h[k] + c₁ * h[k + 1] + c₂ * h[k + 2] + c₃ * h[k + 3]) :
-- imply
  ∃ e f g : Fin 4, ∃ α β γ δ A B C D : ℂ, ∀ n : ℕ,
    h[n] =
      A * α ^ n +
        B * n.descFactorial e * β ^ (n - e) +
        C * n.descFactorial f * γ ^ (n - f) +
        D * n.descFactorial g * δ ^ (n - g) := by
-- proof
  let vec4 (a b c d : ℂ) : Fin 4 → ℂ :=
    Matrix.vecCons a (Matrix.vecCons b (Matrix.vecCons c (Matrix.vecCons d Matrix.vecEmpty)))
  let mat4 (r0 r1 r2 r3 : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
    Matrix.of (Matrix.vecCons r0 (Matrix.vecCons r1 (Matrix.vecCons r2 (Matrix.vecCons r3 Matrix.vecEmpty))))
  let p : ℂ[X] := X ^ 4 - C c₃ * X ^ 3 - C c₂ * X ^ 2 - C c₁ * X - C c₀
  have hle : p.natDegree ≤ 4 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    have h4 : m ≠ 4 := by omega
    have h3 : m ≠ 3 := by omega
    have h2 : m ≠ 2 := by omega
    have h1 : m ≠ 1 := by omega
    have h0 : m ≠ 0 := by omega
    simp [p, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X, h0, h1.symm, h2, h3, h4]
  have hco4 : p.coeff 4 = 1 := by
    simp [p, coeff_sub, coeff_C_mul, coeff_X_pow]
  have hnat : p.natDegree = 4 := natDegree_eq_of_le_of_coeff_ne_zero hle (by simp [hco4])
  have hmonic : p.Monic := by
    rw [Monic.def, leadingCoeff, hnat, hco4]
  have hdeg : p.degree ≠ 0 := by
    rw [degree_eq_natDegree]
    · simp [hnat]
    ·
      intro hp0
      simp [hp0] at hnat
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root p hdeg
  have rootEq (z : ℂ) (hz : p.eval z = 0) :
    z ^ 4 = c₃ * z ^ 3 + c₂ * z ^ 2 + c₁ * z + c₀ := by
    simp only [p, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hz
    linear_combination hz
  have hαeq : α ^ 4 = c₃ * α ^ 3 + c₂ * α ^ 2 + c₁ * α + c₀ := rootEq α hα
  obtain ⟨q, hq⟩ := (dvd_iff_isRoot (p := p) (a := α)).mpr hα
  have hqmonic : q.Monic :=
    Monic.of_mul_monic_left (monic_X_sub_C α) (by simpa [hq] using hmonic)
  have hqdeg : q.natDegree = 3 := by
    have hmul := Monic.natDegree_mul (monic_X_sub_C α) hqmonic
    rw [← hq, hnat, natDegree_X_sub_C] at hmul
    omega
  have hqdeg0 : q.degree ≠ 0 := by
    rw [degree_eq_natDegree hqmonic.ne_zero]
    simp [hqdeg]
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root q hqdeg0
  obtain ⟨r, hr⟩ := (dvd_iff_isRoot (p := q) (a := β)).mpr hβ
  have hrmonic : r.Monic :=
    Monic.of_mul_monic_left (monic_X_sub_C β) (by simpa [hr] using hqmonic)
  have hrdeg : r.natDegree = 2 := by
    have hmul := Monic.natDegree_mul (monic_X_sub_C β) hrmonic
    rw [← hr, hqdeg, natDegree_X_sub_C] at hmul
    omega
  have hrdeg0 : r.degree ≠ 0 := by
    rw [degree_eq_natDegree hrmonic.ne_zero]
    simp [hrdeg]
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_root r hrdeg0
  obtain ⟨s, hs⟩ := (dvd_iff_isRoot (p := r) (a := γ)).mpr hγ
  have hsmonic : s.Monic :=
    Monic.of_mul_monic_left (monic_X_sub_C γ) (by simpa [hs] using hrmonic)
  have hsdeg : s.natDegree = 1 := by
    have hmul := Monic.natDegree_mul (monic_X_sub_C γ) hsmonic
    rw [← hs, hrdeg, natDegree_X_sub_C] at hmul
    omega
  set δ := -s.coeff 0
  have hsform : s = X - C δ := by
    ext n
    if hn0 : n = 0 then
      simp [hn0, δ, coeff_X, coeff_C]
    else
      if hn1 : n = 1 then
        have hlead : s.coeff 1 = 1 := by
          rwa [Monic.def, leadingCoeff, hsdeg] at hsmonic
        simp [hn1, hlead, coeff_X, δ]
      else
        have hgt : 1 < n := by omega
        have hs0 : s.coeff n = 0 :=
          coeff_eq_zero_of_natDegree_lt (by simpa [hsdeg] using hgt)
        simp [hs0, coeff_X, coeff_C, hn0, δ]
        exact Ne.symm hn1
  have hp : p = (X - C α) * (X - C β) * (X - C γ) * (X - C δ) := by
    rw [hq, hr, hs, hsform]
    ring
  have hβeq : β ^ 4 = c₃ * β ^ 3 + c₂ * β ^ 2 + c₁ * β + c₀ := by
    apply rootEq
    rw [hp]
    simp [eval_mul, eval_sub, eval_X, eval_C]
  have hγeq : γ ^ 4 = c₃ * γ ^ 3 + c₂ * γ ^ 2 + c₁ * γ + c₀ := by
    apply rootEq
    rw [hp]
    simp [eval_mul, eval_sub, eval_X, eval_C]
  have hδeq : δ ^ 4 = c₃ * δ ^ 3 + c₂ * δ ^ 2 + c₁ * δ + c₀ := by
    apply rootEq
    rw [hp]
    simp [eval_mul, eval_sub, eval_X, eval_C]
  have hgeom (z : ℂ) (hz : z ^ 4 = c₃ * z ^ 3 + c₂ * z ^ 2 + c₁ * z + c₀) :
    ∀ k, z ^ (k + 4) =
        c₀ * z ^ k + c₁ * z ^ (k + 1) + c₂ * z ^ (k + 2) + c₃ * z ^ (k + 3) := by
    intro k
    calc
      _ = z ^ k * z ^ 4 := by ring
      _ = z ^ k * (c₃ * z ^ 3 + c₂ * z ^ 2 + c₁ * z + c₀) := by rw [hz]
      _ = c₀ * z ^ k + c₁ * z ^ (k + 1) + c₂ * z ^ (k + 2) + c₃ * z ^ (k + 3) := by ring
  have quad (ρ : ℂ)
    (hp4 : X ^ 4 - C c₃ * X ^ 3 - C c₂ * X ^ 2 - C c₁ * X - C c₀ = (X - C ρ) ^ 4) :
      ∃ e f g : Fin 4, ∃ α' β' γ' δ' A B C D : ℂ, ∀ n : ℕ,
        h[n] =
          A * α' ^ n +
            B * n.descFactorial e * β' ^ (n - e) +
            C * n.descFactorial f * γ' ^ (n - f) +
            D * n.descFactorial g * δ' ^ (n - g) := by
    have h3 := congrArg (fun t => t.coeff 3) hp4
    have h2 := congrArg (fun t => t.coeff 2) hp4
    have h1 := congrArg (fun t => t.coeff 1) hp4
    have h0 := congrArg (fun t => t.coeff 0) hp4
    simp [coeff_sub, coeff_C_mul, coeff_X, coeff_C, pow_succ, mul_sub, sub_mul] at h3 h2 h1 h0
    have hc₃ : c₃ = 4 * ρ := by
      ring_nf at h3
      linear_combination -h3
    have hc₂ : c₂ = -(6 * ρ ^ 2) := by
      ring_nf at h2
      linear_combination -h2
    have hc₁ : c₁ = 4 * ρ ^ 3 := by
      ring_nf at h1
      linear_combination -h1
    have hc₀ : c₀ = -(ρ ^ 4) := by
      ring_nf at h0
      linear_combination -h0
    have hd1 (n : ℕ) : (n.descFactorial 1 : ℂ) = n := by simp
    have hd2 (n : ℕ) : (n.descFactorial 2 : ℂ) = (n : ℂ) * ((n : ℂ) - 1) := by
      cases n with
      | zero => simp [Nat.descFactorial_succ]
      | succ n =>
        simp [Nat.descFactorial_succ]
        ring
    have hd3 (n : ℕ) : (n.descFactorial 3 : ℂ) =
        (n : ℂ) * ((n : ℂ) - 1) * ((n : ℂ) - 2) := by
      cases n with
      | zero => simp [Nat.descFactorial_succ]
      | succ n =>
        cases n with
        | zero => simp [Nat.descFactorial_succ]
        | succ n =>
          simp [Nat.descFactorial_succ]
          ring
    if hρ : ρ = 0 then
      have hc₀0 : c₀ = 0 := by simpa [hρ] using hc₀
      have hc₁0 : c₁ = 0 := by simpa [hρ] using hc₁
      have hc₂0 : c₂ = 0 := by simpa [hρ] using hc₂
      have hc₃0 : c₃ = 0 := by simpa [hρ] using hc₃
      refine ⟨1, 2, 3, 0, 0, 0, 0, h[0], h[1], h[2] / 2, h[3] / 6, ?_⟩
      intro n
      match n with
      | 0 => simp
      | 1 => simp [Nat.descFactorial_succ]
      | 2 => simp [Nat.descFactorial_succ]
      | 3 => simp [Nat.descFactorial_succ]
      | n + 4 =>
        have hz : h[n + 4] = 0 := by
          simpa [hc₀0, hc₁0, hc₂0, hc₃0] using hrec n
        rw [hz]
        simp [zero_pow (show n + 4 ≠ 0 by omega), zero_pow (show n + 3 ≠ 0 by omega),
          zero_pow (show n + 2 ≠ 0 by omega), zero_pow (show n + 1 ≠ 0 by omega)]
    else
      set A : ℂ := h[0] with hA
      set B : ℂ := h[1] / ρ - A with hB
      set C : ℂ := (h[2] / ρ ^ 2 - A - 2 * B) / 2 with hC
      set D : ℂ := (h[3] / ρ ^ 3 - A - 3 * B - 6 * C) / 6 with hD
      have hpoly : ∀ n, h[n] =
          (A + B * (n : ℂ) + C * (n : ℂ) * ((n : ℂ) - 1) +
            D * (n : ℂ) * ((n : ℂ) - 1) * ((n : ℂ) - 2)) * ρ ^ n := by
        intro n
        induction n using Nat.stepInduction 4 with
        | base i hi =>
          interval_cases i
          · simp [hA]
          ·
            simp [hB, hA]
            field_simp [hρ]
          ·
            simp [hC, hB, hA]
            field_simp [hρ]
            ring
          ·
            simp [hD, hC, hB, hA]
            field_simp [hρ]
            ring
        | step k ih =>
          have ih0 := ih 0 (by decide)
          have ih1 := ih 1 (by decide)
          have ih2 := ih 2 (by decide)
          have ih3 := ih 3 (by decide)
          simp only [Nat.add_zero] at ih0
          rw [hrec k, ih0, ih1, ih2, ih3, hc₀, hc₁, hc₂, hc₃]
          push_cast
          ring
      refine ⟨1, 2, 3, ρ, ρ, ρ, ρ, A, B * ρ, C * ρ ^ 2, D * ρ ^ 3, ?_⟩
      intro n
      rw [hpoly n]
      simp only [show ((1 : Fin 4) : ℕ) = 1 from rfl, show ((2 : Fin 4) : ℕ) = 2 from rfl,
        show ((3 : Fin 4) : ℕ) = 3 from rfl, hd1, hd2, hd3]
      if hn3 : n < 3 then
        interval_cases n
        · simp
        ·
          simp
          ring
        ·
          simp
          ring
      else
        have hge3 : 3 ≤ n := by omega
        have hge2 : 2 ≤ n := by omega
        have hge1 : 1 ≤ n := by omega
        have hp1 : ρ ^ n = ρ ^ (n - 1) * ρ := calc
          _ = ρ ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hge1]
          _ = ρ ^ (n - 1) * ρ := pow_succ ρ (n - 1)
        have hp2 : ρ ^ n = ρ ^ (n - 2) * ρ ^ 2 := calc
          _ = ρ ^ (n - 2 + 2) := by rw [Nat.sub_add_cancel hge2]
          _ = ρ ^ (n - 2) * ρ ^ 2 := by rw [pow_add]
        have hp3 : ρ ^ n = ρ ^ (n - 3) * ρ ^ 3 := calc
          _ = ρ ^ (n - 3 + 3) := by rw [Nat.sub_add_cancel hge3]
          _ = ρ ^ (n - 3) * ρ ^ 3 := by rw [pow_add]
        have hBterm : (B * (n : ℂ)) * ρ ^ n = B * ρ * (n : ℂ) * ρ ^ (n - 1) := by
          rw [hp1]
          ring
        have hCterm :
          (C * (n : ℂ) * ((n : ℂ) - 1)) * ρ ^ n =
              C * ρ ^ 2 * ((n : ℂ) * ((n : ℂ) - 1)) * ρ ^ (n - 2) := by
          rw [hp2]
          ring
        have hDterm :
          (D * (n : ℂ) * ((n : ℂ) - 1) * ((n : ℂ) - 2)) * ρ ^ n =
              D * ρ ^ 3 * ((n : ℂ) * ((n : ℂ) - 1) * ((n : ℂ) - 2)) * ρ ^ (n - 3) := by
          rw [hp3]
          ring
        calc
          _ = A * ρ ^ n + (B * (n : ℂ)) * ρ ^ n + (C * (n : ℂ) * ((n : ℂ) - 1)) * ρ ^ n +
              (D * (n : ℂ) * ((n : ℂ) - 1) * ((n : ℂ) - 2)) * ρ ^ n := by
            ring
          _ = A * ρ ^ n + B * ρ * (n : ℂ) * ρ ^ (n - 1) +
              C * ρ ^ 2 * ((n : ℂ) * ((n : ℂ) - 1)) * ρ ^ (n - 2) +
              D * ρ ^ 3 * ((n : ℂ) * ((n : ℂ) - 1) * ((n : ℂ) - 2)) * ρ ^ (n - 3) := by
            rw [hBterm, hCterm, hDterm]
  have solveFrom (s0 s1 s2 s3 : ℕ → ℂ)
    (hs0 : ∀ k, s0 (k + 4) =
        c₀ * s0 k + c₁ * s0 (k + 1) + c₂ * s0 (k + 2) + c₃ * s0 (k + 3))
      (hs1 : ∀ k, s1 (k + 4) =
        c₀ * s1 k + c₁ * s1 (k + 1) + c₂ * s1 (k + 2) + c₃ * s1 (k + 3))
      (hs2 : ∀ k, s2 (k + 4) =
        c₀ * s2 k + c₁ * s2 (k + 1) + c₂ * s2 (k + 2) + c₃ * s2 (k + 3))
      (hs3 : ∀ k, s3 (k + 4) =
        c₀ * s3 k + c₁ * s3 (k + 1) + c₂ * s3 (k + 2) + c₃ * s3 (k + 3))
      (hdet : IsUnit (Matrix.of fun (i j : Fin 4) =>
        vec4 (s0 (i : ℕ)) (s1 (i : ℕ)) (s2 (i : ℕ)) (s3 (i : ℕ)) j).det) :
      ∃ A B C D : ℂ, ∀ n, h[n] = s0 n * A + s1 n * B + s2 n * C + s3 n * D := by
    let M : Matrix (Fin 4) (Fin 4) ℂ :=
      Matrix.of fun (i j : Fin 4) =>
        vec4 (s0 (i : ℕ)) (s1 (i : ℕ)) (s2 (i : ℕ)) (s3 (i : ℕ)) j
    let b : Fin 4 → ℂ := vec4 h[0] h[1] h[2] h[3]
    let cvec : Fin 4 → ℂ := Matrix.mulVec M⁻¹ b
    have hc : cvec = Matrix.mulVec M⁻¹ b := rfl
    have hMc : Matrix.mulVec M cvec = b := by
      rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hdet, Matrix.one_mulVec]
    let A : ℂ := cvec 0
    let B : ℂ := cvec 1
    let C : ℂ := cvec 2
    let D : ℂ := cvec 3
    have hrow (i : Fin 4) :
      h[(i : ℕ)] = s0 (i : ℕ) * A + s1 (i : ℕ) * B + s2 (i : ℕ) * C + s3 (i : ℕ) * D := by
      have hsum := congrFun hMc i
      rw [Matrix.mulVec_apply_eq_sum] at hsum
      simp [M, vec4, Fin.sum_univ_succ] at hsum
      calc
        _ = b i := by
          fin_cases i <;> simp [b, vec4]
        _ = s0 (i : ℕ) * cvec 0 + (s1 (i : ℕ) * cvec 1 +
            (s2 (i : ℕ) * cvec 2 + s3 (i : ℕ) * cvec 3)) := by
          rw [← hsum]
        _ = s0 (i : ℕ) * A + s1 (i : ℕ) * B + s2 (i : ℕ) * C + s3 (i : ℕ) * D := by
          simp [A, B, C, D]
          ring
    refine ⟨A, B, C, D, ?_⟩
    intro n
    induction n using Nat.stepInduction 4 with
    | base i hi =>
      interval_cases i
      · simpa using hrow ⟨0, by decide⟩
      · simpa using hrow ⟨1, by decide⟩
      · simpa using hrow ⟨2, by decide⟩
      · simpa using hrow ⟨3, by decide⟩
    | step k ih =>
      have ih0 := ih 0 (by decide)
      have ih1 := ih 1 (by decide)
      have ih2 := ih 2 (by decide)
      have ih3 := ih 3 (by decide)
      simp only [Nat.add_zero] at ih0
      have hclose :
        c₀ * (s0 k * A + s1 k * B + s2 k * C + s3 k * D) +
            c₁ * (s0 (k + 1) * A + s1 (k + 1) * B + s2 (k + 1) * C + s3 (k + 1) * D) +
            c₂ * (s0 (k + 2) * A + s1 (k + 2) * B + s2 (k + 2) * C + s3 (k + 2) * D) +
            c₃ * (s0 (k + 3) * A + s1 (k + 3) * B + s2 (k + 3) * C + s3 (k + 3) * D) =
          s0 (k + 4) * A + s1 (k + 4) * B + s2 (k + 4) * C + s3 (k + 4) * D := calc
        _ = (c₀ * s0 k + c₁ * s0 (k + 1) + c₂ * s0 (k + 2) + c₃ * s0 (k + 3)) * A +
            (c₀ * s1 k + c₁ * s1 (k + 1) + c₂ * s1 (k + 2) + c₃ * s1 (k + 3)) * B +
            (c₀ * s2 k + c₁ * s2 (k + 1) + c₂ * s2 (k + 2) + c₃ * s2 (k + 3)) * C +
            (c₀ * s3 k + c₁ * s3 (k + 1) + c₂ * s3 (k + 2) + c₃ * s3 (k + 3)) * D := by
          ring
        _ = s0 (k + 4) * A + s1 (k + 4) * B + s2 (k + 4) * C + s3 (k + 4) * D := by
          rw [← hs0 k, ← hs1 k, ← hs2 k, ← hs3 k]
      rw [hrec k, ih0, ih1, ih2, ih3, hclose]
  have triple (ρ σ : ℂ) (hne : ρ ≠ σ)
    (hp3 : X ^ 4 - C c₃ * X ^ 3 - C c₂ * X ^ 2 - C c₁ * X - C c₀ =
        (X - C ρ) ^ 3 * (X - C σ)) :
      ∃ e f g : Fin 4, ∃ α' β' γ' δ' A B C D : ℂ, ∀ n : ℕ,
        h[n] =
          A * α' ^ n +
            B * n.descFactorial e * β' ^ (n - e) +
            C * n.descFactorial f * γ' ^ (n - f) +
            D * n.descFactorial g * δ' ^ (n - g) := by
    have h3c := congrArg (fun t => t.coeff 3) hp3
    have h2c := congrArg (fun t => t.coeff 2) hp3
    have h1c := congrArg (fun t => t.coeff 1) hp3
    have h0c := congrArg (fun t => t.coeff 0) hp3
    simp only [pow_succ, mul_add, add_mul, sub_eq_add_neg] at h3c h2c h1c h0c
    simp [coeff_add, coeff_neg, coeff_C_mul, coeff_mul_X, coeff_X, coeff_C] at h3c h2c h1c h0c
    have hc₃ : c₃ = 3 * ρ + σ := by
      ring_nf at h3c
      linear_combination -h3c
    have hc₂ : c₂ = -(3 * ρ ^ 2 + 3 * ρ * σ) := by
      ring_nf at h2c
      linear_combination -h2c
    have hc₁ : c₁ = ρ ^ 3 + 3 * ρ ^ 2 * σ := by
      ring_nf at h1c
      linear_combination -h1c
    have hc₀ : c₀ = -(ρ ^ 3 * σ) := by
      ring_nf at h0c
      linear_combination -h0c
    have hd2 (n : ℕ) : (n.descFactorial 2 : ℂ) = (n : ℂ) * ((n : ℂ) - 1) := by
      cases n with
      | zero => simp [Nat.descFactorial_succ]
      | succ n =>
        simp [Nat.descFactorial_succ]
        ring
    if hρ : ρ = 0 then
      have hc₀0 : c₀ = 0 := by simpa [hρ] using hc₀
      have hc₁0 : c₁ = 0 := by simpa [hρ] using hc₁
      have hc₂0 : c₂ = 0 := by simpa [hρ] using hc₂
      have hc₃σ : c₃ = σ := by simpa [hρ] using hc₃
      have hσ0 : σ ≠ 0 := by
        intro h
        apply hne
        rw [hρ, h]
      set G : ℂ := h[3] / σ ^ 3 with hG
      set A : ℂ := h[0] - G with hA
      set B : ℂ := h[1] - G * σ with hB
      set C : ℂ := (h[2] - G * σ ^ 2) / 2 with hC
      refine ⟨1, 2, 0, ρ, ρ, ρ, σ, A, B, C, G, ?_⟩
      intro n
      induction n using Nat.stepInduction 4 with
      | base i hi =>
        interval_cases i
        · simp [hρ, hA, Nat.descFactorial_zero]
        · simp [hρ, hA, hB, Nat.descFactorial_zero, Nat.descFactorial_succ, pow_one]
        · simp [hρ, hA, hB, hC, Nat.descFactorial_zero, Nat.descFactorial_succ]
        ·
          simp [hρ, hA, hB, hC, hG, Nat.descFactorial_zero, Nat.descFactorial_succ]
          field_simp [hσ0]
      | step k ih =>
        have ih3 := ih 3 (by decide)
        simp [hρ, Nat.descFactorial_zero, Nat.descFactorial_succ,
          zero_pow (show k + 3 ≠ 0 by omega), zero_pow (show k + 2 ≠ 0 by omega),
          zero_pow (show k + 1 ≠ 0 by omega)] at ih3
        rw [hrec k, hc₀0, hc₁0, hc₂0, hc₃σ, ih3]
        simp [hρ, Nat.descFactorial_zero, Nat.descFactorial_succ,
          zero_pow (show k + 4 ≠ 0 by omega), zero_pow (show k + 3 ≠ 0 by omega),
          zero_pow (show k + 2 ≠ 0 by omega), pow_succ]
        ring
    else
      set G : ℂ :=
        (h[3] - 3 * ρ * h[2] + 3 * ρ ^ 2 * h[1] - ρ ^ 3 * h[0]) / (σ - ρ) ^ 3 with hG
      set A : ℂ := h[0] - G with hA
      set B : ℂ := (h[1] - G * σ) / ρ - A with hB
      set C : ℂ := (h[2] / ρ ^ 2 - G * σ ^ 2 / ρ ^ 2 - A - 2 * B) / 2 with hC
      have hpoly : ∀ n, h[n] =
          (A + B * (n : ℂ) + C * (n : ℂ) * ((n : ℂ) - 1)) * ρ ^ n + G * σ ^ n := by
        intro n
        induction n using Nat.stepInduction 4 with
        | base i hi =>
          interval_cases i
          · simp [hA]
          ·
            simp only [hA, hB]
            field_simp [hρ]
            ring
          ·
            simp only [hA, hB, hC]
            field_simp [hρ]
            ring
          ·
            simp only [hA, hB, hC, hG]
            field_simp [hρ, sub_ne_zero.mpr (Ne.symm hne)]
            ring
        | step k ih =>
          have ih0 := ih 0 (by decide)
          have ih1 := ih 1 (by decide)
          have ih2 := ih 2 (by decide)
          have ih3 := ih 3 (by decide)
          simp only [Nat.add_zero] at ih0
          rw [hrec k, ih0, ih1, ih2, ih3, hc₀, hc₁, hc₂, hc₃]
          push_cast
          ring
      refine ⟨1, 2, 0, ρ, ρ, ρ, σ, A, B * ρ, C * ρ ^ 2, G, ?_⟩
      intro n
      rw [hpoly n]
      simp only [show ((1 : Fin 4) : ℕ) = 1 from rfl, show ((2 : Fin 4) : ℕ) = 2 from rfl,
        show ((0 : Fin 4) : ℕ) = 0 from rfl, Nat.descFactorial_zero, Nat.descFactorial_one,
        Nat.sub_zero, hd2, Nat.cast_one, mul_one]
      if hn : n < 2 then
        interval_cases n
        · simp
        ·
          simp
          ring
      else
        have hge2 : 2 ≤ n := by omega
        have hge1 : 1 ≤ n := by omega
        have hp1 : ρ ^ n = ρ ^ (n - 1) * ρ := calc
          _ = ρ ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hge1]
          _ = ρ ^ (n - 1) * ρ := pow_succ ρ (n - 1)
        have hp2 : ρ ^ n = ρ ^ (n - 2) * ρ ^ 2 := calc
          _ = ρ ^ (n - 2 + 2) := by rw [Nat.sub_add_cancel hge2]
          _ = ρ ^ (n - 2) * ρ ^ 2 := by rw [pow_add]
        have hBterm : (B * (n : ℂ)) * ρ ^ n = B * ρ * (n : ℂ) * ρ ^ (n - 1) := by
          rw [hp1]
          ring
        have hCterm : (C * (n : ℂ) * ((n : ℂ) - 1)) * ρ ^ n =
            C * ρ ^ 2 * ((n : ℂ) * ((n : ℂ) - 1)) * ρ ^ (n - 2) := by
          rw [hp2]
          ring
        calc
          _ = A * ρ ^ n + (B * (n : ℂ)) * ρ ^ n + (C * (n : ℂ) * ((n : ℂ) - 1)) * ρ ^ n +
              G * σ ^ n := by
            ring
          _ = A * ρ ^ n + B * ρ * (n : ℂ) * ρ ^ (n - 1) +
              C * ρ ^ 2 * ((n : ℂ) * ((n : ℂ) - 1)) * ρ ^ (n - 2) + G * σ ^ n := by
            rw [hBterm, hCterm]
  have transfer (z : ℂ) (hz : z ≠ 0)
    (hψ : ∀ k : ℕ,
        ((k + 4 : ℕ) : ℂ) * z ^ (k + 4) =
          c₀ * (((k : ℕ) : ℂ) * z ^ k) +
            c₁ * (((k + 1 : ℕ) : ℂ) * z ^ (k + 1)) +
            c₂ * (((k + 2 : ℕ) : ℂ) * z ^ (k + 2)) +
            c₃ * (((k + 3 : ℕ) : ℂ) * z ^ (k + 3)))
      (k : ℕ) :
      ((k + 4 : ℕ) : ℂ) * z ^ ((k + 4) - 1) =
        c₀ * ((k : ℂ) * z ^ (k - 1)) +
          c₁ * (((k + 1 : ℕ) : ℂ) * z ^ ((k + 1) - 1)) +
          c₂ * (((k + 2 : ℕ) : ℂ) * z ^ ((k + 2) - 1)) +
          c₃ * (((k + 3 : ℕ) : ℂ) * z ^ ((k + 3) - 1)) := by
    have hs (n : ℕ) : ((n : ℕ) : ℂ) * z ^ n = z * (((n : ℕ) : ℂ) * z ^ (n - 1)) := by
      if hn : n = 0 then
        simp [hn]
      else
        have hge : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hpow : z ^ n = z * z ^ (n - 1) := calc
          _ = z ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hge]
          _ = z ^ (n - 1) * z := pow_succ z (n - 1)
          _ = z * z ^ (n - 1) := by ring
        rw [hpow]
        ring
    have h := hψ k
    rw [hs (k + 4), hs k, hs (k + 1), hs (k + 2), hs (k + 3)] at h
    apply mul_left_cancel₀ hz
    convert h using 1; ring
  have double (ρ σ τ : ℂ) (hρσ : ρ ≠ σ) (hρτ : ρ ≠ τ) (hστ : σ ≠ τ)
    (hp2 : X ^ 4 - C c₃ * X ^ 3 - C c₂ * X ^ 2 - C c₁ * X - C c₀ =
        (X - C ρ) ^ 2 * (X - C σ) * (X - C τ)) :
      ∃ e f g : Fin 4, ∃ α' β' γ' δ' A B C D : ℂ, ∀ n : ℕ,
        h[n] =
          A * α' ^ n +
            B * n.descFactorial e * β' ^ (n - e) +
            C * n.descFactorial f * γ' ^ (n - f) +
            D * n.descFactorial g * δ' ^ (n - g) := by
    have h3c := congrArg (fun t => t.coeff 3) hp2
    have h2c := congrArg (fun t => t.coeff 2) hp2
    have h1c := congrArg (fun t => t.coeff 1) hp2
    have h0c := congrArg (fun t => t.coeff 0) hp2
    simp only [pow_succ, mul_add, add_mul, sub_eq_add_neg] at h3c h2c h1c h0c
    simp [coeff_add, coeff_neg, coeff_C_mul, coeff_mul_X, coeff_X, coeff_C] at h3c h2c h1c h0c
    have hc₃ : c₃ = 2 * ρ + σ + τ := by
      ring_nf at h3c
      linear_combination -h3c
    have hc₂ : c₂ = -(ρ ^ 2 + 2 * ρ * (σ + τ) + σ * τ) := by
      ring_nf at h2c
      linear_combination -h2c
    have hc₁ : c₁ = ρ ^ 2 * (σ + τ) + 2 * ρ * σ * τ := by
      ring_nf at h1c
      linear_combination -h1c
    have hc₀ : c₀ = -(ρ ^ 2 * σ * τ) := by
      ring_nf at h0c
      linear_combination -h0c
    have hρ4 : ρ ^ 4 = c₃ * ρ ^ 3 + c₂ * ρ ^ 2 + c₁ * ρ + c₀ := by
      rw [hc₃, hc₂, hc₁, hc₀]
      ring
    have hσ4 : σ ^ 4 = c₃ * σ ^ 3 + c₂ * σ ^ 2 + c₁ * σ + c₀ := by
      rw [hc₃, hc₂, hc₁, hc₀]
      ring
    have hτ4 : τ ^ 4 = c₃ * τ ^ 3 + c₂ * τ ^ 2 + c₁ * τ + c₀ := by
      rw [hc₃, hc₂, hc₁, hc₀]
      ring
    let s0 : ℕ → ℂ := fun n => ρ ^ n
    let s1 : ℕ → ℂ := fun n => (n : ℂ) * ρ ^ (n - 1)
    let s2 : ℕ → ℂ := fun n => σ ^ n
    let s3 : ℕ → ℂ := fun n => τ ^ n
    have hs0 : ∀ k, s0 (k + 4) = c₀ * s0 k + c₁ * s0 (k + 1) + c₂ * s0 (k + 2) + c₃ * s0 (k + 3) := by
      intro k
      simpa [s0] using hgeom ρ hρ4 k
    have hs2 : ∀ k, s2 (k + 4) = c₀ * s2 k + c₁ * s2 (k + 1) + c₂ * s2 (k + 2) + c₃ * s2 (k + 3) := by
      intro k
      simpa [s2] using hgeom σ hσ4 k
    have hs3 : ∀ k, s3 (k + 4) = c₀ * s3 k + c₁ * s3 (k + 1) + c₂ * s3 (k + 2) + c₃ * s3 (k + 3) := by
      intro k
      simpa [s3] using hgeom τ hτ4 k
    have hψ : ∀ k, ((k + 4 : ℕ) : ℂ) * ρ ^ (k + 4) =
        c₀ * (((k : ℕ) : ℂ) * ρ ^ k) +
          c₁ * (((k + 1 : ℕ) : ℂ) * ρ ^ (k + 1)) +
          c₂ * (((k + 2 : ℕ) : ℂ) * ρ ^ (k + 2)) +
          c₃ * (((k + 3 : ℕ) : ℂ) * ρ ^ (k + 3)) := by
      intro k
      rw [hc₀, hc₁, hc₂, hc₃]
      push_cast
      ring
    have hs1 : ∀ k, s1 (k + 4) = c₀ * s1 k + c₁ * s1 (k + 1) + c₂ * s1 (k + 2) + c₃ * s1 (k + 3) := by
      intro k
      if hρ0 : ρ = 0 then
        subst hρ0
        simp [s1, hc₀, hc₁]
      else
        simpa [s1] using transfer ρ hρ0 hψ k
    have hdet : IsUnit (Matrix.of fun (i j : Fin 4) =>
        vec4 (s0 (i : ℕ)) (s1 (i : ℕ)) (s2 (i : ℕ)) (s3 (i : ℕ)) j).det := by
      have hM :
        Matrix.of (fun (i j : Fin 4) =>
            vec4 (s0 (i : ℕ)) (s1 (i : ℕ)) (s2 (i : ℕ)) (s3 (i : ℕ)) j) =
            mat4 (vec4 1 0 1 1) (vec4 ρ 1 σ τ)
              (vec4 (ρ ^ 2) (2 * ρ) (σ ^ 2) (τ ^ 2))
              (vec4 (ρ ^ 3) (3 * ρ ^ 2) (σ ^ 3) (τ ^ 3)) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [vec4, mat4, s0, s1, s2, s3, pow_zero, pow_one]
      have hdetM :
        (mat4 (vec4 1 0 1 1) (vec4 ρ 1 σ τ)
          (vec4 (ρ ^ 2) (2 * ρ) (σ ^ 2) (τ ^ 2))
          (vec4 (ρ ^ 3) (3 * ρ ^ 2) (σ ^ 3) (τ ^ 3))).det =
            (σ - ρ) ^ 2 * (τ - ρ) ^ 2 * (τ - σ) := by
        rw [Matrix.det_succ_row_zero]
        have h22 : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := by decide
        have h32 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := by decide
        simp [vec4, mat4, Matrix.det_fin_three, Fin.sum_univ_succ, Matrix.submatrix_apply, h22, h32]
        ring
      rw [hM, hdetM]
      refine isUnit_iff_ne_zero.mpr ?_
      apply mul_ne_zero
      ·
        apply mul_ne_zero
        · exact pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hρσ))
        · exact pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hρτ))
      · exact sub_ne_zero.mpr (Ne.symm hστ)
    obtain ⟨A, B, C, D, hn⟩ := solveFrom s0 s1 s2 s3 hs0 hs1 hs2 hs3 hdet
    refine ⟨1, 0, 0, ρ, ρ, σ, τ, A, B, C, D, ?_⟩
    intro n
    have h := hn n
    simp [s0, s1, s2, s3, Nat.descFactorial_zero, Nat.cast_one, mul_one] at h ⊢
    convert h using 1
    ring
  have pair (ρ σ : ℂ) (hρσ : ρ ≠ σ)
    (hp2 : X ^ 4 - C c₃ * X ^ 3 - C c₂ * X ^ 2 - C c₁ * X - C c₀ =
        (X - C ρ) ^ 2 * (X - C σ) ^ 2) :
      ∃ e f g : Fin 4, ∃ α' β' γ' δ' A B C D : ℂ, ∀ n : ℕ,
        h[n] =
          A * α' ^ n +
            B * n.descFactorial e * β' ^ (n - e) +
            C * n.descFactorial f * γ' ^ (n - f) +
            D * n.descFactorial g * δ' ^ (n - g) := by
    have h3c := congrArg (fun t => t.coeff 3) hp2
    have h2c := congrArg (fun t => t.coeff 2) hp2
    have h1c := congrArg (fun t => t.coeff 1) hp2
    have h0c := congrArg (fun t => t.coeff 0) hp2
    simp only [pow_succ, mul_add, add_mul, sub_eq_add_neg, mul_assoc] at h3c h2c h1c h0c
    simp [coeff_add, coeff_neg, coeff_C_mul, coeff_mul_X, coeff_X, coeff_C] at h3c h2c h1c h0c
    have hc₃ : c₃ = 2 * (ρ + σ) := by
      ring_nf at h3c
      linear_combination -h3c
    have hc₂ : c₂ = -(ρ ^ 2 + 4 * ρ * σ + σ ^ 2) := by
      ring_nf at h2c
      linear_combination -h2c
    have hc₁ : c₁ = 2 * ρ * σ * (ρ + σ) := by
      ring_nf at h1c
      linear_combination -h1c
    have hc₀ : c₀ = -(ρ ^ 2 * σ ^ 2) := by
      ring_nf at h0c
      linear_combination -h0c
    have hρ4 : ρ ^ 4 = c₃ * ρ ^ 3 + c₂ * ρ ^ 2 + c₁ * ρ + c₀ := by
      rw [hc₃, hc₂, hc₁, hc₀]
      ring
    have hσ4 : σ ^ 4 = c₃ * σ ^ 3 + c₂ * σ ^ 2 + c₁ * σ + c₀ := by
      rw [hc₃, hc₂, hc₁, hc₀]
      ring
    let s0 : ℕ → ℂ := fun n => ρ ^ n
    let s1 : ℕ → ℂ := fun n => (n : ℂ) * ρ ^ (n - 1)
    let s2 : ℕ → ℂ := fun n => σ ^ n
    let s3 : ℕ → ℂ := fun n => (n : ℂ) * σ ^ (n - 1)
    have hs0 : ∀ k, s0 (k + 4) = c₀ * s0 k + c₁ * s0 (k + 1) + c₂ * s0 (k + 2) + c₃ * s0 (k + 3) := by
      intro k
      simpa [s0] using hgeom ρ hρ4 k
    have hs2 : ∀ k, s2 (k + 4) = c₀ * s2 k + c₁ * s2 (k + 1) + c₂ * s2 (k + 2) + c₃ * s2 (k + 3) := by
      intro k
      simpa [s2] using hgeom σ hσ4 k
    have hψρ : ∀ k, ((k + 4 : ℕ) : ℂ) * ρ ^ (k + 4) =
        c₀ * (((k : ℕ) : ℂ) * ρ ^ k) +
          c₁ * (((k + 1 : ℕ) : ℂ) * ρ ^ (k + 1)) +
          c₂ * (((k + 2 : ℕ) : ℂ) * ρ ^ (k + 2)) +
          c₃ * (((k + 3 : ℕ) : ℂ) * ρ ^ (k + 3)) := by
      intro k
      rw [hc₀, hc₁, hc₂, hc₃]
      push_cast
      ring
    have hψσ : ∀ k, ((k + 4 : ℕ) : ℂ) * σ ^ (k + 4) =
        c₀ * (((k : ℕ) : ℂ) * σ ^ k) +
          c₁ * (((k + 1 : ℕ) : ℂ) * σ ^ (k + 1)) +
          c₂ * (((k + 2 : ℕ) : ℂ) * σ ^ (k + 2)) +
          c₃ * (((k + 3 : ℕ) : ℂ) * σ ^ (k + 3)) := by
      intro k
      rw [hc₀, hc₁, hc₂, hc₃]
      push_cast
      ring
    have hs1 : ∀ k, s1 (k + 4) = c₀ * s1 k + c₁ * s1 (k + 1) + c₂ * s1 (k + 2) + c₃ * s1 (k + 3) := by
      intro k
      if hρ0 : ρ = 0 then
        subst hρ0
        simp [s1, hc₀, hc₁]
      else
        simpa [s1] using transfer ρ hρ0 hψρ k
    have hs3 : ∀ k, s3 (k + 4) = c₀ * s3 k + c₁ * s3 (k + 1) + c₂ * s3 (k + 2) + c₃ * s3 (k + 3) := by
      intro k
      if hσ0 : σ = 0 then
        subst hσ0
        simp [s3, hc₀, hc₁]
      else
        simpa [s3] using transfer σ hσ0 hψσ k
    have hdet : IsUnit (Matrix.of fun (i j : Fin 4) =>
        vec4 (s0 (i : ℕ)) (s1 (i : ℕ)) (s2 (i : ℕ)) (s3 (i : ℕ)) j).det := by
      have hM :
        Matrix.of (fun (i j : Fin 4) =>
            vec4 (s0 (i : ℕ)) (s1 (i : ℕ)) (s2 (i : ℕ)) (s3 (i : ℕ)) j) =
            mat4 (vec4 1 0 1 0) (vec4 ρ 1 σ 1)
              (vec4 (ρ ^ 2) (2 * ρ) (σ ^ 2) (2 * σ))
              (vec4 (ρ ^ 3) (3 * ρ ^ 2) (σ ^ 3) (3 * σ ^ 2)) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [vec4, mat4, s0, s1, s2, s3, pow_zero, pow_one]
      have hdetM :
        (mat4 (vec4 1 0 1 0) (vec4 ρ 1 σ 1)
          (vec4 (ρ ^ 2) (2 * ρ) (σ ^ 2) (2 * σ))
          (vec4 (ρ ^ 3) (3 * ρ ^ 2) (σ ^ 3) (3 * σ ^ 2))).det =
            (σ - ρ) ^ 4 := by
        rw [Matrix.det_succ_row_zero]
        have h22 : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := by decide
        simp [vec4, mat4, Matrix.det_fin_three, Fin.sum_univ_succ, Matrix.submatrix_apply, h22]
        ring
      rw [hM, hdetM]
      exact isUnit_iff_ne_zero.mpr (pow_ne_zero 4 (sub_ne_zero.mpr (Ne.symm hρσ)))
    obtain ⟨A, B, C, D, hn⟩ := solveFrom s0 s1 s2 s3 hs0 hs1 hs2 hs3 hdet
    refine ⟨1, 0, 1, ρ, ρ, σ, σ, A, B, C, D, ?_⟩
    intro n
    have h := hn n
    simp [s0, s1, s2, s3, Nat.descFactorial_zero, Nat.cast_one, mul_one] at h ⊢
    convert h using 1
    ring
  have distinct
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαδ : α ≠ δ)
      (hβγ : β ≠ γ) (hβδ : β ≠ δ) (hγδ : γ ≠ δ) :
      ∃ e f g : Fin 4, ∃ α' β' γ' δ' A B C D : ℂ, ∀ n : ℕ,
        h[n] =
          A * α' ^ n +
            B * n.descFactorial e * β' ^ (n - e) +
            C * n.descFactorial f * γ' ^ (n - f) +
            D * n.descFactorial g * δ' ^ (n - g) := by
    let v : Fin 4 → ℂ := vec4 α β γ δ
    have hinj : Function.Injective v := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [v, vec4] at hij
      · rfl
      · exact absurd hij hαβ
      · exact absurd hij hαγ
      · exact absurd hij hαδ
      · exact absurd hij (Ne.symm hαβ)
      · rfl
      · exact absurd hij hβγ
      · exact absurd hij hβδ
      · exact absurd hij (Ne.symm hαγ)
      · exact absurd hij (Ne.symm hβγ)
      · rfl
      · exact absurd hij hγδ
      · exact absurd hij (Ne.symm hαδ)
      · exact absurd hij (Ne.symm hβδ)
      · exact absurd hij (Ne.symm hγδ)
      · rfl
    let s0 : ℕ → ℂ := fun n => α ^ n
    let s1 : ℕ → ℂ := fun n => β ^ n
    let s2 : ℕ → ℂ := fun n => γ ^ n
    let s3 : ℕ → ℂ := fun n => δ ^ n
    have hs0 := hgeom α hαeq
    have hs1 := hgeom β hβeq
    have hs2 := hgeom γ hγeq
    have hs3 := hgeom δ hδeq
    let M : Matrix (Fin 4) (Fin 4) ℂ := (Matrix.vandermonde v).transpose
    have hdet : IsUnit (Matrix.of fun (i j : Fin 4) =>
        vec4 (s0 (i : ℕ)) (s1 (i : ℕ)) (s2 (i : ℕ)) (s3 (i : ℕ)) j).det := by
      have hM : Matrix.of (fun (i j : Fin 4) =>
          vec4 (s0 (i : ℕ)) (s1 (i : ℕ)) (s2 (i : ℕ)) (s3 (i : ℕ)) j) = M := by
        ext i j
        fin_cases j <;> simp [M, s0, s1, s2, s3, v, vec4, Matrix.vandermonde_apply, Matrix.transpose_apply]
      rw [hM]
      simpa [M, Matrix.det_transpose] using
        isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
    obtain ⟨A, B, C, D, hn⟩ := solveFrom s0 s1 s2 s3 hs0 hs1 hs2 hs3 hdet
    refine ⟨0, 0, 0, α, β, γ, δ, A, B, C, D, ?_⟩
    intro n
    have h := hn n
    simp [s0, s1, s2, s3, Nat.descFactorial_zero, Nat.cast_one, mul_one] at h ⊢
    convert h using 1
    ring
  if hαβ : α = β then
    suffices ∃ e f g : Fin 4, ∃ α' β' γ' δ' A B C D : ℂ, ∀ n : ℕ,
        h[n] =
          A * α' ^ n +
            B * n.descFactorial e * β' ^ (n - e) +
            C * n.descFactorial f * γ' ^ (n - f) +
            D * n.descFactorial g * δ' ^ (n - g) by
      exact this
    if hαγ : α = γ then
      suffices ∃ e f g : Fin 4, ∃ α' β' γ' δ' A B C D : ℂ, ∀ n : ℕ,
          h[n] =
            A * α' ^ n +
              B * n.descFactorial e * β' ^ (n - e) +
              C * n.descFactorial f * γ' ^ (n - f) +
              D * n.descFactorial g * δ' ^ (n - g) by
        exact this
      if hαδ : α = δ then
        apply quad α
        simp only [hαβ.symm, hαγ.symm, hαδ.symm] at hp
        simp [p] at hp
        rw [hp]
        ring
      else
        apply triple α δ hαδ
        simp only [hαβ.symm, hαγ.symm] at hp
        simp [p] at hp
        rw [hp]
        ring
    else
      suffices _ from this
      if hαδ : α = δ then
        apply triple α γ hαγ
        simp only [hαβ.symm, hαδ.symm] at hp
        simp [p] at hp
        rw [hp]
        ring
      else
        suffices _ from this
        if hγδ : γ = δ then
          apply pair α γ hαγ
          simp only [hαβ.symm, hγδ.symm] at hp
          simp [p] at hp
          rw [hp]
          ring
        else
          apply double α γ δ hαγ hαδ hγδ
          simp only [hαβ.symm] at hp
          simp [p] at hp
          rw [hp]
          ring
  else
    suffices ∃ e f g : Fin 4, ∃ α' β' γ' δ' A B C D : ℂ, ∀ n : ℕ,
        h[n] =
          A * α' ^ n +
            B * n.descFactorial e * β' ^ (n - e) +
            C * n.descFactorial f * γ' ^ (n - f) +
            D * n.descFactorial g * δ' ^ (n - g) by
      exact this
    if hαγ : α = γ then
      suffices _ from this
      if hαδ : α = δ then
        apply triple α β hαβ
        simp only [hαγ.symm, hαδ.symm] at hp
        simp [p] at hp
        rw [hp]
        ring
      else
        suffices _ from this
        if hβδ : β = δ then
          apply pair α β hαβ
          simp only [hαγ.symm, hβδ.symm] at hp
          simp [p] at hp
          rw [hp]
          ring
        else
          apply double α β δ hαβ hαδ hβδ
          simp only [hαγ.symm] at hp
          simp [p] at hp
          rw [hp]
          ring
    else
      suffices _ from this
      if hαδ : α = δ then
        suffices _ from this
        if hβγ : β = γ then
          apply pair β α (Ne.symm hαβ)
          simp only [hαδ.symm, hβγ.symm] at hp
          simp [p] at hp
          rw [hp]
          ring
        else
          apply double α β γ hαβ hαγ hβγ
          simp only [hαδ.symm] at hp
          simp [p] at hp
          rw [hp]
          ring
      else
        suffices _ from this
        if hβγ : β = γ then
          suffices _ from this
          if hβδ : β = δ then
            apply triple β α (Ne.symm hαβ)
            simp only [hβγ.symm, hβδ.symm] at hp
            simp [p] at hp
            rw [hp]
            ring
          else
            apply double β α δ (Ne.symm hαβ) hβδ hαδ
            simp only [hβγ.symm] at hp
            simp [p] at hp
            rw [hp]
            ring
        else
          suffices _ from this
          if hβδ : β = δ then
            apply double β α γ (Ne.symm hαβ) hβγ hαγ
            simp only [hβδ.symm] at hp
            simp [p] at hp
            rw [hp]
            ring
          else
            suffices _ from this
            if hγδ : γ = δ then
              apply double γ α β (Ne.symm hαγ) (Ne.symm hβγ) hαβ
              simp only [hγδ.symm] at hp
              simp [p] at hp
              rw [hp]
              ring
            else
              exact distinct hαβ hαγ hαδ hβγ hβδ hγδ


-- created on 2026-10-25
