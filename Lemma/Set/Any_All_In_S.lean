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

@[path]
private lemma main
  {s : Set F}
-- given
  (hs : s ∈ nhds (0 : F)) :
-- imply
  ∃ δ : Γ, ∀ y : F, Valued.v y < (δ : WithZero (Multiplicative ℤ)) → y ∈ s := by
-- proof
  obtain ⟨γ, hγ⟩ := (Valued.is_topological_valuation _).mp hs
  have hb : MonoidWithZeroHom.ValueGroup₀.embedding γ.val ≠ (0 : WithZero (Multiplicative ℤ)) := by
    intro h
    exact γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective (h.trans (map_zero _).symm))
  refine ⟨Units.mk0 _ hb, fun y hy => ?_⟩
  apply hγ
  show Valued.v.restrict y < γ.val
  rw [Valuation.restrict_lt_iff_lt_embedding]
  simpa using hy

end LocalGL2.Kirillov

end


-- created on 2026-10-25
