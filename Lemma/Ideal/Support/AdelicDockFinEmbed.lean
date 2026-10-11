import Mathlib
import sympy.Basic
import Lemma.AdicCompletion.IsCompact.LocalLevelOne

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AdicCompletion

/-! FLT AdelicDock / AdelicLevel axioms for finEmbed–localEmbed level-one lemmas. -/

axiom AdelicLevel.idealBound_eq_one_of_not_dvd
  {R : Type*} [CommRing R] [IsDedekindDomain R] {N : Ideal R} (hN : N ≠ ⊥)
  {v : HeightOneSpectrum R} (hv : ¬ v.asIdeal ∣ N) : AdelicLevel.idealBound R N v = 1

def integralSubgroup (R K : Type*) [CommRing R] [Field K] [Algebra R K] :
  Subgroup (GL (Fin 2) K) :=
  (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range

axiom levelOne (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [NumberField K] (N : Ideal R) : Subgroup (GL (Fin 2) (AdeleRing R K))

axiom finiteAdelicGL2Subgroup (K : Type*) [Field K] [NumberField K] :
  Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))

axiom glArch (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [NumberField K] :
  GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (InfiniteAdeleRing K)

axiom glFin (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [NumberField K] :
  GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (FiniteAdeleRing R K)

axiom finComponent (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [NumberField K] (w : HeightOneSpectrum R) :
  GL (Fin 2) (FiniteAdeleRing R K) →* GL (Fin 2) (w.adicCompletion K)

axiom localEmbed (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R) :
  GL (Fin 2) (v.adicCompletion K) →* GL (Fin 2) (FiniteAdeleRing R K)

axiom finEmbed (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [NumberField K] :
  GL (Fin 2) (FiniteAdeleRing R K) →* GL (Fin 2) (AdeleRing R K)

axiom glArch_finEmbed (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [NumberField K] (g : GL (Fin 2) (FiniteAdeleRing R K)) :
  glArch R K (finEmbed R K g) = 1

axiom glFin_finEmbed (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [NumberField K] (g : GL (Fin 2) (FiniteAdeleRing R K)) :
  glFin R K (finEmbed R K g) = g

axiom finComponent_localEmbed_self (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [NumberField K] (v : HeightOneSpectrum R)
  (g : GL (Fin 2) (v.adicCompletion K)) : finComponent R K v (localEmbed R K v g) = g

axiom finComponent_localEmbed_of_ne (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [NumberField K] (v : HeightOneSpectrum R)
  (g : GL (Fin 2) (v.adicCompletion K)) {w : HeightOneSpectrum R}
  (hw : w ≠ v) : finComponent R K w (localEmbed R K v g) = 1

axiom mem_inf_of_components
  (F : Type*) [Field F] [NumberField F] {N : Ideal (𝓞 F)}
  {h : GL (Fin 2) (AdeleRing (𝓞 F) F)} (harch : glArch (𝓞 F) F h = 1)
  (hfin : ∀ w : HeightOneSpectrum (𝓞 F),
    finComponent (𝓞 F) F w (glFin (𝓞 F) F h) ∈ AdelicDock.localLevelOne (𝓞 F) F w N) :
  h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F
