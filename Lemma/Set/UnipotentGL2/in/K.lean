import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.ContinuousUnipotentGL2
import Lemma.Set.Any_All_In_S
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Nat
open Set


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

@[path]
private lemma main
  {K₀ : Subgroup G}
-- given
  (hK : IsOpen (K₀ : Set G)) :
-- imply
  ∃ δ : Γ, ∀ z : F, Valued.v z < (δ : WithZero (Multiplicative ℤ)) → unipotentGL2 z ∈ K₀ := by
-- proof
  apply Set.Any_All_In_S v
  apply (hK.preimage (Nat.ContinuousUnipotentGL2 v)).mem_nhds
  show unipotentGL2 (0 : F) ∈ K₀
  simpa [unipotentGL2_zero] using K₀.one_mem

end LocalGL2.Kirillov

end


-- created on 2026-10-25
