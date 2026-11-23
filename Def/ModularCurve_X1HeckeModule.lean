import Lemma.LaurentSeries.X1HeckeOperator
import Theorem.UpperHalfPlane.X1Diamond
import Def.ModularCurve_JZeroTateModule
import Mathlib.Algebra.MvPolynomial.CommRing
import Abbrev.ModularCurve_X1HeckeModule

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace ModularCurve

open AlgebraicCurve

def heckeGenOne (ℓ : Nat.Primes) : HeckeAlgOne := MvPolynomial.X (Sum.inl ℓ)

def diamondGen (d : ℕ) : HeckeAlgOne := MvPolynomial.X (Sum.inr d)

section Operators

variable (M : ℕ)

def heckeOperatorOneBar (ℓ : Nat.Primes) : Module.End ℤ (JOne M) :=
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  (heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ).toIntLinearMap

def heckeDiamondGenBar : Nat.Primes ⊕ ℕ → Module.End ℤ (JOne M) :=
  Sum.elim (heckeOperatorOneBar M) (diamondOneBar M)

def HeckeDiamondCommuteBar : Prop :=
  ∀ i j : Nat.Primes ⊕ ℕ,
    heckeDiamondGenBar M i * heckeDiamondGenBar M j = heckeDiamondGenBar M j * heckeDiamondGenBar M i

def HeckeDiamondInputsAll : Prop :=
  (∀ ℓ : Nat.Primes,
      haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
      HeckeInputsOneAlong (AlgebraicClosure ℚ) M ℓ) ∧
    ∀ d : ℕ, Nat.Coprime d M →
      (∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ) ∧
        ∃ σ' : x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M,
          IsBaseChangeAutOf (AlgebraicClosure ℚ) (diamondAut M d) σ'

end Operators

section Eval

variable {M : ℕ}

open scoped IsMulCommutative in

def heckeEvalOneBarAux (h : HeckeDiamondCommuteBar M) :
    HeckeAlgOne →ₐ[ℤ] (Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M)) :
      Subalgebra ℤ (Module.End ℤ (JOne M))) :=
  haveI := isMulCommutative_adjoin_heckeDiamondGenBar h
  MvPolynomial.aeval fun i =>
    (⟨heckeDiamondGenBar M i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ :
      Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M)))

def heckeEvalOneBar (h : HeckeDiamondCommuteBar M) : HeckeAlgOne →+* Module.End ℤ (JOne M) :=
  ((Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M))).val.comp (heckeEvalOneBarAux h)).toRingHom

end Eval

section TheModule

variable (M : ℕ)

open Classical in

@[implicit_reducible]
def heckeModuleOneBar : Module HeckeAlgOne (JOne M) :=
  if h : HeckeDiamondCommuteBar M then Module.compHom (JOne M) (heckeEvalOneBar h)
  else Module.compHom (JOne M)
    (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes ⊕ ℕ → ℤ))

variable {M}

end TheModule

section Integral

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlgOne J]

def tateHeckeRepOne : HeckeAlgOne →+* Module.End ℤ_[p] (TateModule p J) where
  toMonoidHom := TateModule.rep p J HeckeAlgOne
  map_zero' := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    show (0 : HeckeAlgOne) • (x : ℕ → J) n = 0
    exact zero_smul HeckeAlgOne ((x : ℕ → J) n)
  map_add' s t := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
    show (s + t) • (x : ℕ → J) n = s • (x : ℕ → J) n + t • (x : ℕ → J) n
    exact add_smul s t ((x : ℕ → J) n)

end Integral

section Rational

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlgOne J]

def rationalHeckeRepOne : HeckeAlgOne →+* Module.End ℚ_[p] (RationalTateModule p J) :=
  (Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J)).toRingHom.comp (tateHeckeRepOne p J)

def rationalHeckeAlgebraOne : Subalgebra ℚ_[p] (Module.End ℚ_[p] (RationalTateModule p J)) :=
  Algebra.adjoin ℚ_[p] (Set.range (rationalHeckeRepOne p J))

def rationalDiamondOne (d : ℕ) : rationalHeckeAlgebraOne p J :=
  ⟨rationalHeckeRepOne p J (diamondGen d), rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J _⟩

def rationalHeckeOne (ℓ : Nat.Primes) : rationalHeckeAlgebraOne p J :=
  ⟨rationalHeckeRepOne p J (heckeGenOne ℓ), rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J _⟩

end Rational

section Predicate

variable {K L : Type} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlgOne J]
  [DistribMulAction (L ≃ₐ[K] L) J]

def RationalRankTwoNebentypusOf : Prop :=
  ∃ b : Module.Basis (Fin 2) (rationalHeckeAlgebraOne p J) (RationalTateModule p J),
    ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * p →
      ∀ A' : ValuationSubring L, A'.LiesOverPrime ℓ →
        ∀ σ : L ≃ₐ[K] L, A'.IsFrobeniusAt σ ℓ →
          rationalDiamondOne p J ℓ *
              ((b.repr (rationalGaloisRep p J (L ≃ₐ[K] L) σ (b 0))) 0
                  * (b.repr (rationalGaloisRep p J (L ≃ₐ[K] L) σ (b 1))) 1
                - (b.repr (rationalGaloisRep p J (L ≃ₐ[K] L) σ (b 1))) 0
                  * (b.repr (rationalGaloisRep p J (L ≃ₐ[K] L) σ (b 0))) 1)
            = (ℓ : rationalHeckeAlgebraOne p J)

end Predicate

section ModularInstance

def RationalRankTwoNebentypus (M p : ℕ) [Fact p.Prime] [Module HeckeAlgOne (JOne M)] : Prop :=
  RationalRankTwoNebentypusOf (K := ℚ) (L := AlgebraicClosure ℚ) M p (JOne M)

end ModularInstance

end ModularCurve

end
