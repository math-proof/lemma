import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.CoeNegUF
import Lemma.Fin.Dg.eq.A
import Lemma.Fin.WGCoe
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Nat
open Fin


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable (ϖ : (HeightOneSpectrum.adicCompletion K v)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion K v) = WithZero.exp (-1 : ℤ))

@[path]
private lemma main:
-- imply
  wG v * (unipotentGL2 (1 : F) * wG v) =
      unipotentGL2 (1 : F) * (dg v ((negUF v : UF v) : Fx) * (wG v * unipotentGL2 (1 : F))) := by
-- proof
  apply Units.ext
  simp only [Units.val_mul, Fin.WGCoe, Fin.Dg.eq.A, unipotentGL2_coe]
  rw [Nat.CoeNegUF]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
