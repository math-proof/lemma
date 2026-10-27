import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.AutomorphicForm_FormalBaseChange
import Lemma.Int.P2MUtil

open NumberField IsDedekindDomain AutomorphicForm

/--
[AutomorphicForm_formalBaseChange_formalBaseChange](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AutomorphicForm_formalBaseChange_formalBaseChange.lean)
-/

private lemma  C6E4.satakePow_add_two_mul {R : Type*} [CommRing R] (s e : R) :
  ∀ n k : ℕ, satakePow (k + 2 * n) s e = satakePow n s e * satakePow (k + n) s e - e ^ n * satakePow k s e := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro k; simp; ring
  | one => intro k; rw [show k + 2 * 1 = k + 2 by ring, satakePow_add_two, satakePow_one, pow_one]
  | more n ih0 ih1 =>
    intro k
    have h1 := ih1 (k + 1)
    have h0 := ih0 (k + 2)
    rw [show k + 2 * (n + 2) = (k + 2 * n + 2) + 2 by ring, satakePow_add_two,
      show k + 2 * n + 2 + 1 = k + 1 + 2 * (n + 1) by ring, h1,
      show k + 2 * n + 2 = k + 2 + 2 * n by ring, h0, satakePow_add_two n,
      show k + 1 + (n + 1) = k + (n + 2) by ring, show k + 2 + n = k + (n + 2) by ring,
      satakePow_add_two k]
    ring

private lemma  C6E4.satakePow_satakePow {R : Type*} [CommRing R] (m n : ℕ) (s e : R) :
  satakePow m (satakePow n s e) (e ^ n) = satakePow (n * m) s e := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more m ih0 ih1 =>
    rw [satakePow_add_two, ih1, ih0, show n * (m + 2) = n * m + 2 * n by ring,
      C6E4.satakePow_add_two_mul s e n (n * m), show n * m + n = n * (m + 1) by ring]

private lemma  C6E4.formalBaseChange_formalBaseChange
  (F K M : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
  [Algebra (𝓞 K) (𝓞 M)] [Algebra.IsIntegral (𝓞 K) (𝓞 M)]
  [Algebra (𝓞 F) (𝓞 M)] [Algebra.IsIntegral (𝓞 F) (𝓞 M)]
  [IsScalarTower (𝓞 F) (𝓞 K) (𝓞 M)]
  {R : Type*} [CommRing R] (π : HeckeEigensystem F R) :
  formalBaseChange K M (formalBaseChange F K π) = formalBaseChange F M π := by
  have hunder : ∀ 𝔓 : HeightOneSpectrum (𝓞 M), (𝔓.under (𝓞 K)).under (𝓞 F) = 𝔓.under (𝓞 F) := by
    intro 𝔓
    ext1
    exact Ideal.under_under 𝔓.asIdeal
  have hdeg : ∀ 𝔓 : HeightOneSpectrum (𝓞 M),
      (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal = ((𝔓.under (𝓞 K)).under (𝓞 F)).asIdeal.inertiaDeg' (𝔓.under (𝓞 K)).asIdeal
        * (𝔓.under (𝓞 K)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
    intro 𝔓
    rw [hunder]
    haveI : (𝔓.under (𝓞 K)).asIdeal.LiesOver (𝔓.under (𝓞 F)).asIdeal := by
      rw [← hunder]; exact ⟨rfl⟩
    haveI : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 K)).asIdeal := ⟨rfl⟩
    haveI : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 F)).asIdeal := ⟨rfl⟩
    haveI := (𝔓.under (𝓞 F)).isMaximal
    exact Ideal.inertiaDeg_algebra_tower (𝔓.under (𝓞 F)).asIdeal (𝔓.under (𝓞 K)).asIdeal 𝔓.asIdeal
  unfold formalBaseChange
  congr 1
  ·
    funext 𝔓
    simp only []
    rw [hdeg 𝔓, ← C6E4.satakePow_satakePow, hunder]
  ·
    funext 𝔓
    simp only []
    rw [hdeg 𝔓, pow_mul, hunder]
@[path]
private lemma main
  [CommRing R]
  {F K M : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field M] [NumberField M] [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)] [Algebra (𝓞 K) (𝓞 M)] [Algebra.IsIntegral (𝓞 K) (𝓞 M)] [Algebra (𝓞 F) (𝓞 M)] [Algebra.IsIntegral (𝓞 F) (𝓞 M)] [IsScalarTower (𝓞 F) (𝓞 K) (𝓞 M)]
  {π : HeckeEigensystem F R} :
-- imply
  formalBaseChange K M (formalBaseChange F K π) = formalBaseChange F M π :=
-- proof
  C6E4.formalBaseChange_formalBaseChange F K M π


-- created on 2026-10-23
