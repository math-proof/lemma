import Lemma.Definitions.Def_DrinfeldCurve_FunctionField
import Lemma.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Lemma.Definitions.Def_ModularCurve_JZeroTateModule

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace DrinfeldCurve

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]
  (ℓ : ℕ) [Fact ℓ.Prime] (E : Type*) [Field E] [Algebra ℚ_[ℓ] E]

def tateRep : hSubgroup q →*
    Module.End E (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) :=
  (Module.End.baseChangeHom ℚ_[ℓ] E
      (ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) :
    Module.End ℚ_[ℓ]
        (ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) →*
      Module.End E (E ⊗[ℚ_[ℓ]]
        ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)))).comp
    ((ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))
        (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k)).comp (hFunctionFieldAction q k))

abbrev tateProd (S : Type) : Type _ :=
  S → E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))

def tateProdRep (S : Type) : hSubgroup q →* Module.End E (tateProd q k ℓ E S) where
  toFun h := LinearMap.pi fun s => (tateRep q k ℓ E h).comp (LinearMap.proj s)
  map_one' := LinearMap.ext fun v => funext fun s => by simp
  map_mul' x y := LinearMap.ext fun v => funext fun s => by simp

theorem tateProdRep_apply (S : Type) (h : hSubgroup q) (v : tateProd q k ℓ E S) (s : S) :
    tateProdRep q k ℓ E S h v s = tateRep q k ℓ E h (v s) :=
  rfl

end DrinfeldCurve

end
