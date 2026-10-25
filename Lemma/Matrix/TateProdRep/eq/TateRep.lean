import Lemma.DrinfeldCurve.FunctionField
import Lemma.AlgebraicCurve.DivisorClassGroup
import Lemma.ModularCurve.JZeroTateModule
import sympy.Basic
set_option autoImplicit false
open scoped TensorProduct


namespace DrinfeldCurve

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k]
  [IsDomain (CoordRing q k)] (ℓ : ℕ) [Fact ℓ.Prime] (E : Type*) [Field E]
  [Algebra ℚ_[ℓ] E]

abbrev TateEnd : Type _ :=
  Module.End E (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
    (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)))

noncomputable def tateRep : hSubgroup q →* TateEnd q k ℓ E :=
  (Module.End.baseChangeHom ℚ_[ℓ] E
      (ModularCurve.RationalTateModule ℓ
        (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)))).toMonoidHom.comp
    ((ModularCurve.rationalGaloisRep ℓ
        (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))
        (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k)).comp
      (hFunctionFieldAction q k))

abbrev tateProd (S : Type) : Type _ :=
  S → E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
    (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))

noncomputable def tateProdRep (S : Type) : hSubgroup q →* Module.End E (tateProd q k ℓ E S) where
  toFun h := LinearMap.pi fun s => (tateRep q k ℓ E h).comp (LinearMap.proj s)
  map_one' := LinearMap.ext fun v => funext fun s => by simp
  map_mul' x y := LinearMap.ext fun v => funext fun s => by simp

@[path]
private lemma main
-- given
  (h : hSubgroup q)
  (S : Type)
  (v : tateProd q k ℓ E S)
  (s : S) :
-- imply
  tateProdRep q k ℓ E S h v s = tateRep q k ℓ E h (v s) := by
-- proof
  rfl

end DrinfeldCurve


-- created on 2026-10-24
