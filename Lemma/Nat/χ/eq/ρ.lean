import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Complex.ψ.eq.φ
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Complex


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {v} in
@[path]
private lemma main
  {δ : Γ}
  {χ ρ : Ch v δ}
-- given
  (h : ∀ u : UF v, chv χ u = chv ρ u) :
-- imply
  χ = ρ := by
-- proof
  apply Complex.ψ.eq.φ (A := Additive (Qm v δ))
  intro a
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
  have h1 := h u
  unfold chv Ch.toChar at h1
  rwa [hu, ofMul_toMul] at h1

end LocalGL2.Kirillov

end


-- created on 2026-10-25
