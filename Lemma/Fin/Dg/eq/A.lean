import Mathlib
import Initialize.Tactic.Attr.Basic
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
  (a : Fx) :
-- imply
  (dg v a : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; 0, 1] :=
-- proof
  rfl

end LocalGL2.Kirillov

end


-- created on 2026-10-25
