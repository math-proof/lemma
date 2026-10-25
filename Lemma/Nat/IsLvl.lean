import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.UmV.le.UmV
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Nat


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

@[path]
private lemma main
  {δ δ₁ : Γ}
  {f : UF v → X}
-- given
  (h : δ ≤ δ₁)
  (hf : IsLvl v δ₁ f) :
-- imply
  IsLvl v δ f :=
-- proof
  fun u m hm => hf u m (Nat.UmV.le.UmV v h hm)

end LocalGL2.Kirillov

end


-- created on 2026-10-25
