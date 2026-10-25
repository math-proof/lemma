import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.Dg.eq.MulDgS
import Lemma.Complex.RT
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Nat
open Complex


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable (ψ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ)
  (S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ))

@[path]
private lemma main
-- given
  (V : G → ℂ)
  (b a : Fx) :
-- imply
  kirillov v ψ S (rT v (dg v b) V) a = kirillov v ψ S V (a * b) := by
-- proof
  unfold kirillov
  rw [Complex.RT, Nat.Dg.eq.MulDgS]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
