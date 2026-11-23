module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Notation.LocalGL2_Kirillov
public import Def.LocalGL2_Kirillov
public import Def.AutomorphicForm_ConstantTerm
public import Instance.NumberField_Completion_Finite
public import Theorem.Complex.isOpen_radiusBall

public noncomputable section

open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Complex


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

@[path]
public theorem main
-- given
  (y : F)
  (r : Γ) :
-- imply
  {x : F | Valued.v (x - y) < (r : WithZero (Multiplicative ℤ))} ∈ nhds y :=
-- proof
  ((Complex.isOpen_radiusBall v r).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)

end LocalGL2.Kirillov

end


-- created on 2026-10-25
