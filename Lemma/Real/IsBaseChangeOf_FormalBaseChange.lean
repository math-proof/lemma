import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AutomorphicForm_HeckeEigensystem
import Lemma.Definitions.Def_AutomorphicForm_FormalBaseChange
open IsDedekindDomain NumberField AutomorphicForm


/--
[AutomorphicForm_isBaseChangeOf_formalBaseChange](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AutomorphicForm_isBaseChangeOf_formalBaseChange.lean)
-/
@[path]
private lemma main
  [CommRing R]
  {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K)] [Algebra.IsIntegral (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K)]
  {π : AutomorphicForm.HeckeEigensystem F R} :
-- imply
  AutomorphicForm.IsBaseChangeOf π (AutomorphicForm.formalBaseChange F K π) :=
-- proof
  ⟨∅, fun _ _ => ⟨rfl, rfl⟩⟩


-- created on 2026-10-24
