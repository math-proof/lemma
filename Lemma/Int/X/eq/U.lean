import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Int.U.in.UmV.is.UFnSub.lt.WithZero_Multiplicative
import Lemma.Nat.VU.eq.One
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Int
open Nat


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

@[path]
private lemma main
  {δ : Γ}
  {u x : UF v}
-- given
  (h : Valued.v (((x : Fx) : F) - ((u : Fx) : F)) < (δ : WithZero (Multiplicative ℤ))) :
-- imply
  ((x : Qm v δ) = (u : Qm v δ)) := by
-- proof
  rw [QuotientGroup.eq, Int.U.in.UmV.is.UFnSub.lt.WithZero_Multiplicative]
  have e : (((x⁻¹ * u : UF v) : Fx) : F) - 1 = (((x⁻¹ : UF v) : Fx) : F) * (((u : Fx) : F) - ((x : Fx) : F)) := by
    have h1 : (((x⁻¹ : UF v) : Fx) : F) * ((x : Fx) : F) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    rw [mul_sub, h1, Subgroup.coe_mul, Units.val_mul]
  rwa [e, map_mul, Nat.VU.eq.One, one_mul, Valuation.map_sub_swap]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
