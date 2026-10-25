/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.Valuation.ValuationSubring
import Lemma.Polynomial.HenselFactorization
import Theorem.FieldTheory.PuiseuxTheorem.Part23
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

@[instance_reducible]
noncomputable def puiseux_subfieldAlgebra {K : Type*} [Field K] :
    Algebra (LaurentSeries K) ↥(puiseuxSubfield K) :=
  (puiseux_laurentToSubfield (K := K)).toAlgebra

noncomputable def puiseux_levelToSubfield {K : Type*} [Field K] {n : ℕ}
    (hn : 0 < n) : ↥(puiseuxLevelField K n hn) →+* ↥(puiseuxSubfield K) :=
  (puiseuxLevelField K n hn).subtype.codRestrict (puiseuxSubfield K) fun y ↦ by
    obtain ⟨z, hz⟩ := RingHom.mem_fieldRange.mp y.property
    change (y : HahnSeries Rat K) ∈ puiseuxSubfield K
    rw [← hz]
    exact ⟨n, hn, puiseux_levelHom_atLevel hn z⟩

noncomputable def puiseux_levelToSubfieldAlgHom {K : Type*} [Field K] {n : ℕ}
    (hn : 0 < n) :
    let _ : Algebra (LaurentSeries K) ↥(puiseuxLevelField K n hn) :=
      puiseux_levelAlgebra n hn
    let _ : Algebra (LaurentSeries K) ↥(puiseuxSubfield K) := puiseux_subfieldAlgebra
    ↥(puiseuxLevelField K n hn) →ₐ[LaurentSeries K] ↥(puiseuxSubfield K) := by
  let _ : Algebra (LaurentSeries K) ↥(puiseuxLevelField K n hn) :=
    puiseux_levelAlgebra n hn
  let _ : Algebra (LaurentSeries K) ↥(puiseuxSubfield K) := puiseux_subfieldAlgebra
  exact
    { puiseux_levelToSubfield hn with
      commutes' := fun _ ↦ rfl }

end
end MetaMathlibExt
end MetaMathlibExt
