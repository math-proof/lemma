import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.EqChvS
import Lemma.Nat.CompV
import Lemma.Nat.χ.eq.ρ
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Nat


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

@[path]
private lemma main
  {δ δ' δ'' : Γ}
  {f : UF v → X}
-- given
  (h' : δ' ≤ δ)
  (h'' : δ'' ≤ δ)
  (hf' : IsLvl v δ' f)
  (hf'' : IsLvl v δ'' f)
  (γ : Ch v δ) :
-- imply
  comp v δ' f (refineCh v h' γ) = comp v δ'' f (refineCh v h'' γ) := by
-- proof
  have e1 := Nat.CompV v (min_le_left δ' δ'') hf' (refineCh v h' γ)
  have e2 := Nat.CompV v (min_le_right δ' δ'') hf'' (refineCh v h'' γ)
  rw [← e1, ← e2]
  congr 1
  apply Nat.χ.eq.ρ
  intro u
  rw [Nat.EqChvS, Nat.EqChvS, Nat.EqChvS, Nat.EqChvS]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
