import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.ContinuousZG
import Lemma.Set.F.in.K
import Lemma.Nat.ZGOne
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
  ∃ δ : Γ, ∀ c : Fx, Valued.v ((c : F) - 1) < (δ : WithZero (Multiplicative ℤ)) → zG v c ∈ K₀ :=
-- proof
  Set.F.in.K v K₀ hK _ (Nat.ContinuousZG v) (by simpa [Nat.ZGOne] using K₀.one_mem)

end LocalGL2.Kirillov

end


-- created on 2026-10-25
