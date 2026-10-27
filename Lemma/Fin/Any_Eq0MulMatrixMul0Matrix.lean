import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private abbrev M2 (a b c d : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  Matrix.of (Matrix.vecCons (Matrix.vecCons a (Matrix.vecCons b Matrix.vecEmpty)) (Matrix.vecCons (Matrix.vecCons c (Matrix.vecCons d Matrix.vecEmpty)) Matrix.vecEmpty))

private lemma exists_coprime_mul_add {a b d : ℕ} (hd : d ≠ 0) (hgcd : Nat.gcd a (Nat.gcd b d) = 1) : ∃ p : ℕ, Nat.Coprime (a * p + b) d := by
  classical
  refine ⟨∏ q ∈ d.primeFactors.filter (fun q => ¬ q ∣ b), q, ?_⟩
  set P := ∏ q ∈ d.primeFactors.filter (fun q => ¬ q ∣ b), q with hP
  apply Nat.Coprime.symm
  apply Nat.coprime_of_dvd
  intro q hq hqd hqab
  have hqP : q ∣ P ↔ ¬ q ∣ b := by
    rw [hP]
    rw [Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hq)]
    constructor
    ·
      rintro ⟨q', hq', hqq'⟩
      rw [Finset.mem_filter, Nat.mem_primeFactors] at hq'
      obtain ⟨⟨hq'p, -, -⟩, hq'b⟩ := hq'
      rwa [(Nat.prime_dvd_prime_iff_eq hq hq'p).mp hqq']
    ·
      intro hqb
      exact ⟨q, Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hq, hqd, hd⟩, hqb⟩, dvd_rfl⟩
  if hqb : q ∣ b then
    have hqa : ¬ q ∣ a := by
      intro hqa
      have : q ∣ Nat.gcd a (Nat.gcd b d) := Nat.dvd_gcd hqa (Nat.dvd_gcd hqb hqd)
      rw [hgcd] at this
      apply hq.one_lt.ne' (Nat.dvd_one.mp this)
    have hqaP : q ∣ a * P := (Nat.dvd_add_right hqb).mp (by rwa [add_comm] at hqab)
    obtain h | h := (Nat.Prime.dvd_mul hq).mp hqaP
    ·
      apply hqa h
    ·
      apply (hqP.mp h) hqb
  else
    apply hqb ((Nat.dvd_add_right (Dvd.dvd.mul_left (hqP.mpr hqb) a)).mp hqab)

private lemma helper_main {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N) (hgcd : Nat.gcd a (Nat.gcd b d) = 1) : ∃ γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ, M2 (a : ℤ) (b : ℤ) 0 (d : ℤ) = (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * M2 (N : ℤ) 0 0 1 * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hd : d ≠ 0 := fun h0 => hN (by rw [← had, h0, mul_zero])
  obtain ⟨p, hp⟩ := exists_coprime_mul_add hd hgcd
  set u : ℤ := (a : ℤ) * p + b with hu
  have hcop : IsCoprime u (d : ℤ) := by
    rw [hu]
    have : ((a * p + b : ℕ) : ℤ) = (a : ℤ) * p + b := by
      push_cast
      ring
    rw [← this, Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    apply hp
  obtain ⟨s, t, hst⟩ := hcop
  have hN' : (N : ℤ) = a * d := by exact_mod_cast had.symm
  refine ⟨⟨M2 (-t) (-u) s (-(d : ℤ)), ?_⟩, ⟨M2 (-1) (p : ℤ) ((-s) * a) ((p : ℤ) * s * a - 1), ?_⟩, ?_⟩
  ·
    rw [Matrix.det_fin_two_of]
    linear_combination hst
  ·
    rw [Matrix.det_fin_two_of]
    ring
  ·
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two, hN']
    ext i j
    fin_cases i <;> fin_cases j
    ·
      simp
      linear_combination (-(a : ℤ)) * hst + ((a : ℤ) * s) * hu
    ·
      simp
      linear_combination ((a : ℤ) * p) * hst - ((a : ℤ) * p * s) * hu
    ·
      simp
      ring
    ·
      simp
      ring

/--
[Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one.lean)
-/
@[path]
private lemma main
  {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N) (hgcd : Nat.gcd a (Nat.gcd b d) = 1) :
  -- imply
  ∃ γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ, M2 (a : ℤ) (b : ℤ) 0 (d : ℤ) = (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * M2 (N : ℤ) 0 0 1 * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) :=
  helper_main hN had hgcd


-- created on 2026-10-20
