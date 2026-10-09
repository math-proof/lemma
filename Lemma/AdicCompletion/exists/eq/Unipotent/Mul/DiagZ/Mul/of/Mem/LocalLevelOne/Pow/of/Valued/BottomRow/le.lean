import Mathlib
import sympy.Basic

open IsDedekindDomain NumberField

/--
[AdelicDock_exists_eq_unipotent_mul_diagZ_mul_of_mem_localLevelOne_pow_of_valued_bottomRow_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdelicDock_exists_eq_unipotent_mul_diagZ_mul_of_mem_localLevelOne_pow_of_valued_bottomRow_le.lean)
-/
axiom AdelicLevel.idealBound (R : Type*) [CommRing R] [IsDedekindDomain R] (N : Ideal R)
  (v : HeightOneSpectrum R) : WithZero (Multiplicative ℤ)

axiom AdelicDock.localLevelOne (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (N : Ideal R) :
  Subgroup (GL (Fin 2) (v.adicCompletion K))

axiom unipotent {F : Type*} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
  (y : v.adicCompletion F) : GL (Fin 2) (v.adicCompletion F)

axiom diagZ {F : Type*} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
  (ϖ : v.adicCompletion F) (hπ : ϖ ≠ 0) (n : ℤ) : GL (Fin 2) (v.adicCompletion F)

private lemma coe_unipotent
  {F : Type*}
  [Field F]
  [NumberField F]
  {v : HeightOneSpectrum (𝓞 F)}
  (y : v.adicCompletion F) :
    ((unipotent y : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![1, y; 0, 1] := by
  sorry

private lemma coe_diagZ
  {F : Type*}
  [Field F]
  [NumberField F]
  {v : HeightOneSpectrum (𝓞 F)}
  (ϖ : v.adicCompletion F) (hπ : ϖ ≠ 0) (n : ℤ) :
    ((diagZ ϖ hπ n : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![ϖ ^ n, 0; 0, 1] := by
  sorry

private lemma v_zpow_uniformizer
  {F : Type*}
  [Field F]
  [NumberField F]
  {v : HeightOneSpectrum (𝓞 F)}
  {ϖ : v.adicCompletion F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (n : ℤ) :
    Valued.v (ϖ ^ n) = WithZero.exp (-n) := by
  sorry

private lemma mem_integers_iff
  {F : Type*}
  [Field F]
  [NumberField F]
  {v : HeightOneSpectrum (𝓞 F)}
  (x : v.adicCompletion F) : x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 := by
  sorry

private lemma idealBound_pow
  {F : Type*}
  [Field F]
  [NumberField F]
  {v : HeightOneSpectrum (𝓞 F)}
  (m : ℕ) : AdelicLevel.idealBound (𝓞 F) (v.asIdeal ^ m) v = WithZero.exp (-(m : ℤ)) := by
  sorry

private lemma structure_lemma
  {F : Type*}
  [Field F]
  [NumberField F]
  {v : HeightOneSpectrum (𝓞 F)}
  (ϖ : v.adicCompletionIntegers F) (hπ : (ϖ : v.adicCompletion F) ≠ 0)
  (hϖ : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) (m : ℕ)
  (hB : AdelicLevel.idealBound (𝓞 F) (v.asIdeal ^ m) v < 1)
  (g : GL (Fin 2) (v.adicCompletion F))
  (hc : Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0)
    ≤ AdelicLevel.idealBound (𝓞 F) (v.asIdeal ^ m) v)
  (hd : Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 - 1)
    ≤ AdelicLevel.idealBound (𝓞 F) (v.asIdeal ^ m) v) :
    ∃ (x : v.adicCompletion F) (n : ℤ) (k : GL (Fin 2) (v.adicCompletion F)),
      k ∈ AdelicDock.localLevelOne (𝓞 F) F v (v.asIdeal ^ m) ∧
      g = unipotent x * diagZ (ϖ : v.adicCompletion F) hπ n * k ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det) = WithZero.exp (-n) := by
  sorry

@[path]
private lemma main
  [Field F] [NumberField F]
  {v : HeightOneSpectrum (𝓞 F)}
  {ϖ : v.adicCompletionIntegers F}
  {m : ℕ}
  {g : GL (Fin 2) (v.adicCompletion F)}
-- given
  (hπ : (ϖ : v.adicCompletion F) ≠ 0)
  (hϖ : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
  (hm : 1 ≤ m)
  (hc : Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) ≤ WithZero.exp (-(m : ℤ)))
  (hd : Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 - 1) ≤ WithZero.exp (-(m : ℤ))) :
-- imply
  ∃ (x : v.adicCompletion F) (n : ℤ) (k : GL (Fin 2) (v.adicCompletion F)),
      k ∈ AdelicDock.localLevelOne (𝓞 F) F v (v.asIdeal ^ m) ∧
      g = unipotent x * diagZ (ϖ : v.adicCompletion F) hπ n * k ∧
      Valued.v (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = WithZero.exp (-n) := by
-- proof
  sorry


-- created on 2026-10-09
