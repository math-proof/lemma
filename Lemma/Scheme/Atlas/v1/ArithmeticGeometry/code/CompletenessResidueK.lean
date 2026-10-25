import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.CompletenessResidueK
open AlgebraicGeometry.CompletenessValuationCriterion


/--
[corollary_16_31](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CompletenessResidueK.lean)
-/
@[path]
lemma corollary_16_31
  {k : Type u}
  [Field k]
  [IsAlgClosed k]
  {X : AlgVariety k}
-- given
  (hX : SatisfiesValuationCriterionResidueK X) :
-- imply
  IsCompleteVariety X.carrier := by
-- proof
  apply completeness_valuation_criterion X
  intro Z R
  obtain ⟨R'_val, hle, hkR', Φ, hker, hsurj⟩ :=
    lemma_16_30 Z.toVariety.baseEmbed Z.toVariety.baseEmbed_inj R.valSub R.contains_base
  let R' : ValRingOver Z.toVariety := ⟨R'_val, hkR'⟩
  have hres : HasResidueFieldK R' := ⟨Φ, hker, hsurj⟩
  obtain ⟨P, hP⟩ := hX Z R' hres
  exact ⟨P, fun x hx => hle (hP x hx)⟩


-- created on 2026-10-23
