module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Notation.LocalGL2_Kirillov
public import Def.LocalGL2_Kirillov
public import Def.AutomorphicForm_ConstantTerm
public import Instance.NumberField_Completion_Finite

public noncomputable section

open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

@[path]
public theorem main
-- given
  (δ : Γ)
  (u : UF v) :
-- imply
  u ∈ Um v δ ↔ Valued.v (((u : Fx) : F) - 1) < (δ : WithZero (Multiplicative ℤ)) :=
-- proof
  Iff.rfl

end LocalGL2.Kirillov

end


-- created on 2026-10-25
