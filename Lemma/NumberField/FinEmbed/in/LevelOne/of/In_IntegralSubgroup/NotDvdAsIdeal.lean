import Mathlib
import sympy.Basic

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

/--
[AdelicDock_finEmbed_localEmbed_mem_levelOne_inf_finiteAdelicGL2Subgroup](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdelicDock_finEmbed_localEmbed_mem_levelOne_inf_finiteAdelicGL2Subgroup.lean)
-/
axiom AdelicLevel.idealBound (R : Type*) [CommRing R] [IsDedekindDomain R] (N : Ideal R)
  (v : HeightOneSpectrum R) : WithZero (Multiplicative ℤ)

axiom IsLocalLevelOne (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R) (N : Ideal R)
  (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) : Prop

axiom AdelicDock.localLevelOne (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (N : Ideal R) :
  Subgroup (GL (Fin 2) (v.adicCompletion K))

axiom integralSubgroup {K : Type*} [Field K] (S : ValuationSubring K) (K : Type*) [Semiring K] :
  Subgroup (GL (Fin 2) K)

axiom levelOne (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [NumberField K] (N : Ideal R) :
  Subgroup (GL (Fin 2) (AdeleRing R K))

axiom finiteAdelicGL2Subgroup (K : Type*) [Field K] [NumberField K] :
  Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))

axiom glArch (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [NumberField K] (h : GL (Fin 2) (AdeleRing R K)) :
  GL (Fin 2) (AdeleRing R K)

axiom glFin (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [NumberField K] (h : GL (Fin 2) (AdeleRing R K)) :
  GL (Fin 2) (AdeleRing R K)

axiom finComponent (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [NumberField K] (w : HeightOneSpectrum R)
  (h : GL (Fin 2) (AdeleRing R K)) : GL (Fin 2) (w.adicCompletion K)

axiom localEmbed (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R) (x : GL (Fin 2) (v.adicCompletion K)) :
  GL (Fin 2) (FiniteAdeleRing R K)

axiom finEmbed (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [NumberField K] (g : GL (Fin 2) (FiniteAdeleRing R K)) :
  GL (Fin 2) (AdeleRing R K)

private lemma isLocalLevelOne_of_integral
  (F : Type*)
  [Field F]
  [NumberField F]
  (v : HeightOneSpectrum (𝓞 F))
  {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
  {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)}
  (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers F) :
  IsLocalLevelOne (𝓞 F) F v N m := by
  sorry

private lemma entries_mem_of_mem_integralSubgroup
  (F : Type*)
  [Field F]
  [NumberField F]
  (v : HeightOneSpectrum (𝓞 F))
  {k : GL (Fin 2) (v.adicCompletion F)}
  (hk : k ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)) (i j : Fin 2) :
  (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
  sorry

private lemma mem_localLevelOne_of_mem_integralSubgroup
  (F : Type*)
  [Field F]
  [NumberField F]
  (v : HeightOneSpectrum (𝓞 F))
  {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
  {k : GL (Fin 2) (v.adicCompletion F)}
  (hk : k ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)) :
  k ∈ AdelicDock.localLevelOne (𝓞 F) F v N := by
  sorry

private lemma mem_inf_of_components
  (F : Type*)
  [Field F]
  [NumberField F]
  (v : HeightOneSpectrum (𝓞 F))
  {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
  (harch : glArch (𝓞 F) F h = 1)
  (hfin : ∀ w : HeightOneSpectrum (𝓞 F),
    finComponent (𝓞 F) F w (glFin (𝓞 F) F h) ∈ AdelicDock.localLevelOne (𝓞 F) F w N) :
  h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  sorry

@[path]
private lemma main
  [Field F] [NumberField F]
  {v : HeightOneSpectrum (𝓞 F)}
  {N : Ideal (𝓞 F)}
  {k : GL (Fin 2) (v.adicCompletion F)}
-- given
  (hv : ¬ v.asIdeal ∣ N)
  (hk : k ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)) :
-- imply
  finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v k) ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
-- proof
  sorry


-- created on 2026-10-09
