import sympy.Basic
import Mathlib
import Lemma.AdicCompletion.IsCompact.LocalLevelOne

open IsDedekindDomain NumberField

/-! FLT AdelicDock axioms shared by local-level lemmas (not a rendered path lemma). -/

axiom AdelicLevel.isOpen_setOf_valued_le_idealBound
  (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) {N : Ideal R}
  (hN : N ≠ ⊥) : IsOpen {y : v.adicCompletion K | Valued.v y ≤ AdelicLevel.idealBound R N v}

axiom AdelicLevel.idealBound_pow
  (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  (m : ℕ) : AdelicLevel.idealBound (𝓞 F) (v.asIdeal ^ m) v = WithZero.exp (-(m : ℤ))

axiom unipotent
  (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  (y : v.adicCompletion F) : GL (Fin 2) (v.adicCompletion F)

axiom diagZ
  (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  (ϖ : v.adicCompletion F) (hπ : ϖ ≠ 0) (n : ℤ) : GL (Fin 2) (v.adicCompletion F)

axiom structure_lemma
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
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det) = WithZero.exp (-n))
