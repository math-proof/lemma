import Mathlib
import sympy.Basic

open IsDedekindDomain

/--
[AdelicDock_finEmbed_localEmbed_comm_of_ne](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdelicDock_finEmbed_localEmbed_comm_of_ne.lean)
-/
axiom localEmbed (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R) (x : GL (Fin 2) (v.adicCompletion K)) :
  GL (Fin 2) (FiniteAdeleRing R K)

axiom finEmbed (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (g : GL (Fin 2) (FiniteAdeleRing R K)) :
  GL (Fin 2) (FiniteAdeleRing R K)

@[main]
private lemma main
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {v w : HeightOneSpectrum R}
  {x : GL (Fin 2) (v.adicCompletion K)}
  {y : GL (Fin 2) (w.adicCompletion K)}
-- given
  (hvw : v ≠ w) :
-- imply
  finEmbed R K (localEmbed R K v x) * finEmbed R K (localEmbed R K w y) =
      finEmbed R K (localEmbed R K w y) * finEmbed R K (localEmbed R K v x) := by
-- proof
  sorry


-- created on 2026-10-09
