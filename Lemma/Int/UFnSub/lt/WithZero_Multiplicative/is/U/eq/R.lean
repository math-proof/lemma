import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Int.U.in.UmV.is.UFnSub.lt.WithZero_Multiplicative
import Lemma.Int.X.eq.U
import Lemma.Nat.VU.eq.One
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Int
open Nat


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable (ϖ : (HeightOneSpectrum.adicCompletion K v)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion K v) = WithZero.exp (-1 : ℤ))

@[path]
private lemma main
-- given
  (δ : Γ)
  (u r : UF v) :
-- imply
  Valued.v (((u : Fx) : F) - ((r : Fx) : F)) < (δ : WithZero (Multiplicative ℤ)) ↔ (u : Qm v δ) = (r : Qm v δ) := by
-- proof
  constructor
  ·
    intro h
    exact Int.X.eq.U v δ r u h
  ·
    intro h
    rw [eq_comm, QuotientGroup.eq, Int.U.in.UmV.is.UFnSub.lt.WithZero_Multiplicative] at h
    have e : ((u : Fx) : F) - ((r : Fx) : F) = ((r : Fx) : F) * ((((r⁻¹ * u : UF v) : Fx) : F) - 1) := by
      have h1 : ((r : Fx) : F) * (((r⁻¹ : UF v) : Fx) : F) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
      rw [Subgroup.coe_mul, Units.val_mul, mul_sub, mul_one, ← mul_assoc, h1, one_mul]
    rwa [e, map_mul, Nat.VU.eq.One, one_mul]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
