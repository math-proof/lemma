import Lemma.Definitions.Def_ModularCurve_ArithmeticGalois
import Lemma.Definitions.Def_HeckeGalois_EichlerShimura
import Lemma.Definitions.Def_EllipticCurve_TateModule
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Basis.Defs

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

theorem tateHeckeRep_apply (t : HeckeAlg) :
    tateHeckeRep p J t = TateModule.rep p J HeckeAlg t :=
  rfl

theorem coe_tateHeckeRep_apply_apply (t : HeckeAlg) (x : TateModule p J) (n : ℕ) :
    ((tateHeckeRep p J t x : TateModule p J) : ℕ → J) n = t • (x : ℕ → J) n :=
  rfl

end Integral

section Rational

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J]

abbrev RationalTateModule : Type :=
  ℚ_[p] ⊗[ℤ_[p]] TateModule p J

def rationalGaloisRep (G : Type) [Monoid G] [DistribMulAction G J] :
    G →* Module.End ℚ_[p] (RationalTateModule p J) :=
  (Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J) :
      Module.End ℤ_[p] (TateModule p J) →* Module.End ℚ_[p] (RationalTateModule p J)).comp
    (TateModule.rep p J G)

theorem rationalGaloisRep_apply (G : Type) [Monoid G] [DistribMulAction G J] (g : G) :
    rationalGaloisRep p J G g = (TateModule.rep p J G g).baseChange ℚ_[p] :=
  rfl

theorem rationalGaloisRep_tmul (G : Type) [Monoid G] [DistribMulAction G J] (g : G) (a : ℚ_[p])
    (x : TateModule p J) :
    rationalGaloisRep p J G g (a ⊗ₜ x) = a ⊗ₜ TateModule.rep p J G g x :=
  rfl

variable [Module HeckeAlg J]

def rationalHeckeRep : HeckeAlg →+* Module.End ℚ_[p] (RationalTateModule p J) :=
  (Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J)).toRingHom.comp (tateHeckeRep p J)

theorem rationalHeckeRep_apply (t : HeckeAlg) :
    rationalHeckeRep p J t = (tateHeckeRep p J t).baseChange ℚ_[p] :=
  rfl

theorem rationalHeckeRep_tmul (t : HeckeAlg) (a : ℚ_[p]) (x : TateModule p J) :
    rationalHeckeRep p J t (a ⊗ₜ x) = a ⊗ₜ tateHeckeRep p J t x :=
  rfl

def rationalHeckeAlgebra : Subalgebra ℚ_[p] (Module.End ℚ_[p] (RationalTateModule p J)) :=
  Algebra.adjoin ℚ_[p] (Set.range (rationalHeckeRep p J))

theorem rationalHeckeRep_mem_rationalHeckeAlgebra (t : HeckeAlg) :
    rationalHeckeRep p J t ∈ rationalHeckeAlgebra p J :=
  Algebra.subset_adjoin (Set.mem_range_self t)

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
