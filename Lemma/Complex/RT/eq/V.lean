import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

@[path, simp]
private lemma main
-- given
  (k : G)
  (V : G → ℂ)
  (g : G) :
-- imply
  rT v k V g = V (g * k) :=
-- proof
  rfl

end LocalGL2.Kirillov

end


-- created on 2026-10-25
