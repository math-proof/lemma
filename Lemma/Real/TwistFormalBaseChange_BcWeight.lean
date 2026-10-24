import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_LanglandsTunnell_BcWeight
import Lemma.Int.P2MUtil

open NumberField IsDedekindDomain Matrix AutomorphicForm

/--
[LanglandsTunnell_agrees_formalBaseChange_twist](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LanglandsTunnell_agrees_formalBaseChange_twist.lean)
-/

private def ta_companion {R : Type*} [CommRing R] (s e : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, -e; 1, s]

private lemma ta_sq {R : Type*} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) :
  A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

private lemma ta_pow_add_two {R : Type*} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
  A ^ (k + 2) = A.trace • A ^ (k + 1) - A.det • A ^ k := by
  rw [pow_add, pow_two, ta_sq, mul_sub, Matrix.mul_smul, Matrix.mul_smul, mul_one, ← pow_succ]

private lemma ta_satakePow_trace_det {R : Type*} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) :
  ∀ k : ℕ, satakePow k A.trace A.det = (A ^ k).trace
  | 0 => by simp [Matrix.trace_one]
  | 1 => by simp
  | (k + 2) => by
    rw [satakePow_add_two, ta_satakePow_trace_det A (k + 1), ta_satakePow_trace_det A k,
      ta_pow_add_two, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]

private lemma ta_trace_companion {R : Type*} [CommRing R] (s e : R) : (ta_companion s e).trace = s := by
  simp [ta_companion, Matrix.trace_fin_two]

private lemma ta_det_companion {R : Type*} [CommRing R] (s e : R) : (ta_companion s e).det = e := by
  simp [ta_companion, Matrix.det_fin_two]

private lemma ta_satakePow_eq_trace_companion_pow {R : Type*} [CommRing R] (k : ℕ) (s e : R) :
  satakePow k s e = (ta_companion s e ^ k).trace := by
  rw [← ta_satakePow_trace_det (ta_companion s e) k, ta_trace_companion, ta_det_companion]

private lemma ta_satakePow_smul {R : Type*} [CommRing R] (k : ℕ) (c s e : R) :
  satakePow k (c * s) (c ^ 2 * e) = c ^ k * satakePow k s e := by
  have htr : (c • ta_companion s e).trace = c * s := by
    rw [Matrix.trace_smul, ta_trace_companion, smul_eq_mul]
  have hdet : (c • ta_companion s e).det = c ^ 2 * e := by
    rw [Matrix.det_smul, ta_det_companion, Fintype.card_fin]
  rw [← htr, ← hdet, ta_satakePow_trace_det, smul_pow, Matrix.trace_smul, smul_eq_mul,
    ← ta_satakePow_eq_trace_companion_pow]

private lemma ta_formalBaseChange_twist_a (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)] {R : Type*} [CommRing R]
  (π : HeckeEigensystem F R) (χ : HeightOneSpectrum (𝓞 F) → R) (𝔓 : HeightOneSpectrum (𝓞 K)) :
  (formalBaseChange F K (π.twist χ)).a 𝔓 = ((formalBaseChange F K π).twist (LanglandsTunnell.bcWeight F K χ)).a 𝔓 := by
  rw [formalBaseChange_a, HeckeEigensystem.twist_a, HeckeEigensystem.twist_b, ta_satakePow_smul,
    HeckeEigensystem.twist_a, formalBaseChange_a, LanglandsTunnell.bcWeight_apply]

private lemma ta_formalBaseChange_twist_b (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)] {R : Type*} [CommRing R]
  (π : HeckeEigensystem F R) (χ : HeightOneSpectrum (𝓞 F) → R) (𝔓 : HeightOneSpectrum (𝓞 K)) :
  (formalBaseChange F K (π.twist χ)).b 𝔓 = ((formalBaseChange F K π).twist (LanglandsTunnell.bcWeight F K χ)).b 𝔓 := by
  rw [formalBaseChange_b, HeckeEigensystem.twist_b, mul_pow, ← pow_mul, HeckeEigensystem.twist_b,
    formalBaseChange_b, LanglandsTunnell.bcWeight_apply, ← pow_mul, mul_comm 2]
@[path]
private lemma main
  [CommRing R]
  {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
  {π : HeckeEigensystem F R}
  {χ : HeightOneSpectrum (𝓞 F) → R} :
-- imply
  HeckeEigensystem.AgreesAwayFromFinite (formalBaseChange F K (π.twist χ))
    ((formalBaseChange F K π).twist (LanglandsTunnell.bcWeight F K χ)) :=
-- proof
  ⟨∅, fun 𝔓 _ => ⟨ta_formalBaseChange_twist_a F K π χ 𝔓, ta_formalBaseChange_twist_b F K π χ 𝔓⟩⟩


-- created on 2026-10-23
