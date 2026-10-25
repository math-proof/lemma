import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Set.Any_All_In_S
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Set


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

@[path]
private lemma main
  {K₀ : Subgroup G}
  {f : Fx → G}
-- given
  (hK : IsOpen (K₀ : Set G))
  (hf : Continuous f)
  (hf1 : f 1 ∈ K₀) :
-- imply
  ∃ δ : Γ, ∀ u : Fx, Valued.v ((u : F) - 1) < (δ : WithZero (Multiplicative ℤ)) → f u ∈ K₀ := by
-- proof
  have h1 : (f ⁻¹' (K₀ : Set G)) ∈ nhds (1 : Fx) := (hK.preimage hf).mem_nhds hf1
  rw [Units.isEmbedding_val₀.toIsInducing.nhds_eq_comap] at h1
  obtain ⟨T, hT, hTsub⟩ := Filter.mem_comap.mp h1
  have hT' : T ∈ nhds (1 : F) := hT
  have hc : ContinuousAt (fun y : F => 1 + y) 0 := (continuous_const.add continuous_id).continuousAt
  have h0 : (fun y : F => 1 + y) ⁻¹' T ∈ nhds (0 : F) := hc.preimage_mem_nhds (by simpa using hT')
  obtain ⟨δ, hδ⟩ := Set.Any_All_In_S v h0
  refine ⟨δ, fun u hu => hTsub (by simpa using hδ _ hu)⟩

end LocalGL2.Kirillov

end


-- created on 2026-10-25
