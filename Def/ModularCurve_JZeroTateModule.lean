import Lemma.LaurentSeries.ArithmeticGalois
import Def.HeckeGalois_EichlerShimura
import Lemma.WeierstrassCurve.TateModule
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Basis.Defs
import Abbrev.ModularCurve_JZeroTateModule

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace ModularCurve

section Integral

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]

def tateHeckeRep : HeckeAlg →+* Module.End ℤ_[p] (TateModule p J) where
  toMonoidHom := TateModule.rep p J HeckeAlg
  map_zero' := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    show (0 : HeckeAlg) • (x : ℕ → J) n = 0
    exact zero_smul HeckeAlg ((x : ℕ → J) n)
  map_add' s t := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    show (s + t) • (x : ℕ → J) n = s • (x : ℕ → J) n + t • (x : ℕ → J) n
    exact add_smul s t ((x : ℕ → J) n)

end Integral

section Rational

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J]

def rationalGaloisRep (G : Type) [Monoid G] [DistribMulAction G J] :
    G →* Module.End ℚ_[p] (RationalTateModule p J) :=
  (Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J) :
      Module.End ℤ_[p] (TateModule p J) →* Module.End ℚ_[p] (RationalTateModule p J)).comp
    (TateModule.rep p J G)

variable [Module HeckeAlg J]

def rationalHeckeRep : HeckeAlg →+* Module.End ℚ_[p] (RationalTateModule p J) :=
  (Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J)).toRingHom.comp (tateHeckeRep p J)

def rationalHeckeAlgebra : Subalgebra ℚ_[p] (Module.End ℚ_[p] (RationalTateModule p J)) :=
  Algebra.adjoin ℚ_[p] (Set.range (rationalHeckeRep p J))

end Rational

section Predicate

variable {K L : Type} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]

def RationalRankTwoCyclotomicOf : Prop :=
  ∃ b : Module.Basis (Fin 2) (rationalHeckeAlgebra p J) (RationalTateModule p J),
    ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * p →
      ∀ A' : ValuationSubring L, A'.LiesOverPrime ℓ →
        ∀ σ : L ≃ₐ[K] L, A'.IsFrobeniusAt σ ℓ →
          (b.repr (rationalGaloisRep p J (L ≃ₐ[K] L) σ (b 0))) 0
              * (b.repr (rationalGaloisRep p J (L ≃ₐ[K] L) σ (b 1))) 1
            - (b.repr (rationalGaloisRep p J (L ≃ₐ[K] L) σ (b 1))) 0
              * (b.repr (rationalGaloisRep p J (L ≃ₐ[K] L) σ (b 0))) 1
            = (ℓ : rationalHeckeAlgebra p J)

end Predicate

section ModularInstance

def RationalRankTwoCyclotomic (M p : ℕ) [Fact p.Prime] [Module HeckeAlg (JZero M)] : Prop :=
  RationalRankTwoCyclotomicOf (K := ℚ) (L := AlgebraicClosure ℚ) M p (JZero M)

end ModularInstance

end ModularCurve

end
