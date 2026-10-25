import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.ChvMulUW.eq.MulChvUChvW
import Lemma.Nat.ChvM.eq.One
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Nat


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

@[path]
private lemma main
  {δ : Γ}
-- given
  (τ : Ch v δ) :
-- imply
  IsLvl v δ (chv τ) :=
-- proof
  fun u m hm => by
  rw [Nat.ChvMulUW.eq.MulChvUChvW, Nat.ChvM.eq.One τ hm, mul_one]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
