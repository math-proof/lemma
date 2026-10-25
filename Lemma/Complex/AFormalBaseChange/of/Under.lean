import Mathlib
import sympy.Basic
import Def.AutomorphicForm_FormalBaseChange
import Lemma.Int.P2MUtil

open NumberField IsDedekindDomain AutomorphicForm
open scoped BigOperators NumberField

/--
[AutomorphicForm_formalBaseChange_a_b_eq_of_under_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AutomorphicForm_formalBaseChange_a_b_eq_of_under_eq.lean)
-/
@[path]
private lemma main
  {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  {π : HeckeEigensystem K ℂ}
  {w w' : HeightOneSpectrum (𝓞 L)}
-- given
  (h : HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w') :
-- imply
  ((formalBaseChange K L π).a w, (formalBaseChange K L π).b w) =
      ((formalBaseChange K L π).a w', (formalBaseChange K L π).b w') := by
  have h' : w.asIdeal.under (𝓞 K) = w'.asIdeal.under (𝓞 K) := congrArg HeightOneSpectrum.asIdeal h
  haveI : w.asIdeal.LiesOver (w'.asIdeal.under (𝓞 K)) := ⟨h'.symm⟩
  have hf : (w'.asIdeal.under (𝓞 K)).inertiaDeg' w.asIdeal = (w'.asIdeal.under (𝓞 K)).inertiaDeg' w'.asIdeal := by
-- proof
    rw [Ideal.inertiaDeg'_eq_inertiaDeg, Ideal.inertiaDeg'_eq_inertiaDeg]
    exact Ideal.inertiaDeg_eq_of_isGaloisGroup (w'.asIdeal.under (𝓞 K)) w.asIdeal w'.asIdeal (L ≃ₐ[K] L)
  simp only [formalBaseChange_a, formalBaseChange_b, h]
  rw [show (HeightOneSpectrum.under (𝓞 K) w').asIdeal = w'.asIdeal.under (𝓞 K) from rfl, hf]


-- created on 2026-10-23
