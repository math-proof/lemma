import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.Rep.eq.Q
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Nat


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

@[path]
private lemma main
-- given
  (δ : Γ)
  (q : Qm v δ)
  (u : UF v) :
-- imply
  ((rep v δ q * u⁻¹ : UF v) : Qm v δ) = 1 ↔ q = (u : Qm v δ) := by
-- proof
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, Nat.Rep.eq.Q, mul_inv_eq_one]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
