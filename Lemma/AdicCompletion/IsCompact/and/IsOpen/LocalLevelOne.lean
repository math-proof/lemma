import Mathlib
import sympy.Basic

open IsDedekindDomain NumberField

/--
[AdelicDock_isCompact_and_isOpen_localLevelOne](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdelicDock_isCompact_and_isOpen_localLevelOne.lean)
-/
axiom AdelicLevel.idealBound (R : Type*) [CommRing R] [IsDedekindDomain R] (N : Ideal R)
  (v : HeightOneSpectrum R) : WithZero (Multiplicative ℤ)

axiom AdelicDock.IsLocalLevelOne (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (N : Ideal R)
  (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) : Prop

axiom AdelicDock.localLevelOne (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (N : Ideal R) :
  Subgroup (GL (Fin 2) (v.adicCompletion K))

private lemma setOf_isLocalLevelOne_eq
  (R K : Type*)
  [CommRing R]
  [IsDedekindDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  (v : HeightOneSpectrum R)
  (N : Ideal R) :
  {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | AdelicDock.IsLocalLevelOne R K v N m}
    = ((⋂ i, ⋂ j, (fun m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) => m i j) ⁻¹'
          (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
        ∩ (fun m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) => m 1 0) ⁻¹'
          {y | Valued.v y ≤ AdelicLevel.idealBound R N v})
      ∩ (fun m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) => m 1 1 - 1) ⁻¹'
          {y | Valued.v y ≤ AdelicLevel.idealBound R N v} := by
  sorry

private lemma isOpen_adicCompletionIntegers
  (R K : Type*)
  [CommRing R]
  [IsDedekindDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  (v : HeightOneSpectrum R) :
  IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  sorry

private lemma isOpen_setOf_isLocalLevelOne
  (R K : Type*)
  [CommRing R]
  [IsDedekindDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  (v : HeightOneSpectrum R)
  (N : Ideal R)
  (hN : N ≠ ⊥) :
  IsOpen {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | AdelicDock.IsLocalLevelOne R K v N m} := by
  sorry

private lemma isClosed_setOf_isLocalLevelOne
  (R K : Type*)
  [CommRing R]
  [IsDedekindDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  (v : HeightOneSpectrum R)
  (N : Ideal R) :
  IsClosed {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | AdelicDock.IsLocalLevelOne R K v N m} := by
  sorry

private lemma coe_localLevelOne_eq
  (R K : Type*)
  [CommRing R]
  [IsDedekindDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  (v : HeightOneSpectrum R)
  (N : Ideal R) :
  (AdelicDock.localLevelOne R K v N : Set (GL (Fin 2) (v.adicCompletion K)))
    = (Units.val ⁻¹'
        {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | AdelicDock.IsLocalLevelOne R K v N m})
      ∩ ((fun g : GL (Fin 2) (v.adicCompletion K) =>
            ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⁻¹'
        {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) | AdelicDock.IsLocalLevelOne R K v N m}) := by
  sorry

private lemma isOpen_localLevelOne
  (R K : Type*)
  [CommRing R]
  [IsDedekindDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  (v : HeightOneSpectrum R)
  (N : Ideal R)
  (hN : N ≠ ⊥) :
  IsOpen (AdelicDock.localLevelOne R K v N : Set (GL (Fin 2) (v.adicCompletion K))) := by
  sorry

private lemma isClosed_localLevelOne
  (R K : Type*)
  [CommRing R]
  [IsDedekindDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  (v : HeightOneSpectrum R)
  (N : Ideal R) :
  IsClosed (AdelicDock.localLevelOne R K v N : Set (GL (Fin 2) (v.adicCompletion K))) := by
  sorry

private lemma isCompact_adicCompletionIntegers
  (R K : Type*)
  [CommRing R]
  [IsDedekindDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  (v : HeightOneSpectrum R)
  [Module.Free ℤ R]
  [Module.Finite ℤ R] :
  IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  sorry

private lemma isCompact_setOf_integral
  (R K : Type*)
  [CommRing R]
  [IsDedekindDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  (v : HeightOneSpectrum R)
  [Module.Free ℤ R]
  [Module.Finite ℤ R] :
  IsCompact {g : GL (Fin 2) (v.adicCompletion K) |
    (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
    ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
      ∈ v.adicCompletionIntegers K} := by
  sorry

private lemma isCompact_localLevelOne
  (R K : Type*)
  [CommRing R]
  [IsDedekindDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  (v : HeightOneSpectrum R)
  (N : Ideal R)
  [Module.Free ℤ R]
  [Module.Finite ℤ R] :
  IsCompact (AdelicDock.localLevelOne R K v N : Set (GL (Fin 2) (v.adicCompletion K))) := by
  sorry

@[path]
private lemma main
  [Field K] [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)}
  {N : Ideal (𝓞 K)}
-- given
  (hN : N ≠ ⊥) :
-- imply
  IsCompact (AdelicDock.localLevelOne (𝓞 K) K v N : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      IsOpen (AdelicDock.localLevelOne (𝓞 K) K v N : Set (GL (Fin 2) (v.adicCompletion K))) :=
-- proof
  sorry


-- created on 2026-10-09
