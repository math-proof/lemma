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
  (r : Γ) :
-- imply
  ∃ c : F, Valued.v c = (r : WithZero (Multiplicative ℤ)) := by
-- proof
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hπ' : Valued.v ((π : K) : F) = WithZero.exp (-1 : ℤ) := by
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  refine ⟨((π : K) : F) ^ (-WithZero.log (r : WithZero (Multiplicative ℤ))), ?_⟩
  rw [map_zpow₀, hπ', ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg,
    WithZero.exp_log r.ne_zero]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
