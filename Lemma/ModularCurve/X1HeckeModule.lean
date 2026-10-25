import Lemma.ModularCurve.X1HeckeOperator
import Lemma.ModularCurve.X1Diamond
import Lemma.ModularCurve.JZeroTateModule
import Mathlib.Algebra.MvPolynomial.CommRing
import Abbrev.ModularCurve_X1HeckeModule

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace ModularCurve

open AlgebraicCurve

def heckeGenOne (ℓ : Nat.Primes) : HeckeAlgOne := MvPolynomial.X (Sum.inl ℓ)

def diamondGen (d : ℕ) : HeckeAlgOne := MvPolynomial.X (Sum.inr d)

@[simp] lemma aeval_heckeGenOne {A : Type*} [CommSemiring A] [Algebra ℤ A]
    (a : Nat.Primes ⊕ ℕ → A) (ℓ : Nat.Primes) :
    MvPolynomial.aeval a (heckeGenOne ℓ) = a (Sum.inl ℓ) :=
  MvPolynomial.aeval_X a _

@[simp] lemma aeval_diamondGen {A : Type*} [CommSemiring A] [Algebra ℤ A]
    (a : Nat.Primes ⊕ ℕ → A) (d : ℕ) :
    MvPolynomial.aeval a (diamondGen d) = a (Sum.inr d) :=
  MvPolynomial.aeval_X a _

section Operators

variable (M : ℕ)

def heckeOperatorOneBar (ℓ : Nat.Primes) : Module.End ℤ (JOne M) :=
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  (heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ).toIntLinearMap

theorem heckeOperatorOneBar_apply (ℓ : Nat.Primes) (x : JOne M) :
    heckeOperatorOneBar M ℓ x =
      (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ x) :=
  rfl

def heckeDiamondGenBar : Nat.Primes ⊕ ℕ → Module.End ℤ (JOne M) :=
  Sum.elim (heckeOperatorOneBar M) (diamondOneBar M)

@[simp] theorem heckeDiamondGenBar_inl (ℓ : Nat.Primes) :
    heckeDiamondGenBar M (Sum.inl ℓ) = heckeOperatorOneBar M ℓ := rfl

@[simp] theorem heckeDiamondGenBar_inr (d : ℕ) :
    heckeDiamondGenBar M (Sum.inr d) = diamondOneBar M d := rfl

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

theorem isMulCommutative_adjoin_heckeDiamondGenBar (h : HeckeDiamondCommuteBar M) :
    IsMulCommutative (Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M))) :=
  Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact h i j)

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

theorem heckeEvalOneBar_apply (h : HeckeDiamondCommuteBar M) (t : HeckeAlgOne) :
    heckeEvalOneBar h t = (heckeEvalOneBarAux h t : Module.End ℤ (JOne M)) :=
  rfl

set_option synthInstance.maxHeartbeats 400000 in
open scoped IsMulCommutative in
theorem heckeEvalOneBarAux_X (h : HeckeDiamondCommuteBar M) (i : Nat.Primes ⊕ ℕ) :
    heckeEvalOneBarAux h (MvPolynomial.X i) =
      ⟨heckeDiamondGenBar M i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ :=
  haveI := isMulCommutative_adjoin_heckeDiamondGenBar h
  MvPolynomial.aeval_X _ i

theorem heckeEvalOneBar_X (h : HeckeDiamondCommuteBar M) (i : Nat.Primes ⊕ ℕ) :
    heckeEvalOneBar h (MvPolynomial.X i) = heckeDiamondGenBar M i := by
  rw [heckeEvalOneBar_apply, heckeEvalOneBarAux_X]

theorem heckeEvalOneBar_heckeGenOne (h : HeckeDiamondCommuteBar M) (ℓ : Nat.Primes) :
    heckeEvalOneBar h (heckeGenOne ℓ) = heckeOperatorOneBar M ℓ :=
  heckeEvalOneBar_X h (Sum.inl ℓ)

theorem heckeEvalOneBar_diamondGen (h : HeckeDiamondCommuteBar M) (d : ℕ) :
    heckeEvalOneBar h (diamondGen d) = diamondOneBar M d :=
  heckeEvalOneBar_X h (Sum.inr d)

theorem heckeEvalOneBar_C (h : HeckeDiamondCommuteBar M) (a : ℤ) :
    heckeEvalOneBar h (MvPolynomial.C a) = (a : Module.End ℤ (JOne M)) := by
  rw [← MvPolynomial.algebraMap_eq, eq_intCast, map_intCast]

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

theorem heckeModuleOneBar_smul_def (h : HeckeDiamondCommuteBar M) (t : HeckeAlgOne) (x : JOne M) :
    (letI := heckeModuleOneBar M; t • x) = heckeEvalOneBar h t x := by
  have e : heckeModuleOneBar M = Module.compHom (JOne M) (heckeEvalOneBar h) := dif_pos h
  rw [e]
  rfl

theorem heckeModuleOneBar_heckeGenOne_smul (h : HeckeDiamondCommuteBar M) (ℓ : Nat.Primes)
    (x : JOne M) : (letI := heckeModuleOneBar M; heckeGenOne ℓ • x) = heckeOperatorOneBar M ℓ x := by
  rw [heckeModuleOneBar_smul_def h, heckeEvalOneBar_heckeGenOne]

theorem heckeModuleOneBar_diamondGen_smul (h : HeckeDiamondCommuteBar M) (d : ℕ)
    (x : JOne M) : (letI := heckeModuleOneBar M; diamondGen d • x) = diamondOneBar M d x := by
  rw [heckeModuleOneBar_smul_def h, heckeEvalOneBar_diamondGen]

theorem heckeModuleOneBar_smul_of_not (h : ¬ HeckeDiamondCommuteBar M) (t : HeckeAlgOne) (x : JOne M) :
    (letI := heckeModuleOneBar M; t • x) = MvPolynomial.constantCoeff t • x := by
  have e : heckeModuleOneBar M =
      Module.compHom (JOne M)
        (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes ⊕ ℕ → ℤ)) :=
    dif_neg h
  rw [e]
  show (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes ⊕ ℕ → ℤ) t) • x = _
  rw [MvPolynomial.eval₂Hom_zero_apply, eq_intCast, Int.cast_id]

theorem heckeModuleOneBar_X_smul_of_not (h : ¬ HeckeDiamondCommuteBar M) (i : Nat.Primes ⊕ ℕ)
    (x : JOne M) : (letI := heckeModuleOneBar M; (MvPolynomial.X i : HeckeAlgOne) • x) = 0 := by
  rw [heckeModuleOneBar_smul_of_not h, MvPolynomial.constantCoeff_X, zero_zsmul]

theorem heckeModuleOneBar_C_smul (a : ℤ) (x : JOne M) :
    (letI := heckeModuleOneBar M; (MvPolynomial.C a : HeckeAlgOne) • x) = a • x := by
  by_cases h : HeckeDiamondCommuteBar M
  · rw [heckeModuleOneBar_smul_def h, heckeEvalOneBar_C, Module.End.intCast_apply]
  · rw [heckeModuleOneBar_smul_of_not h, MvPolynomial.constantCoeff_C]

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

theorem tateHeckeRepOne_apply (t : HeckeAlgOne) :
    tateHeckeRepOne p J t = TateModule.rep p J HeckeAlgOne t :=
  rfl

theorem coe_tateHeckeRepOne_apply_apply (t : HeckeAlgOne) (x : TateModule p J) (n : ℕ) :
    ((tateHeckeRepOne p J t x : TateModule p J) : ℕ → J) n = t • (x : ℕ → J) n :=
  rfl

end Integral

section Rational

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlgOne J]

def rationalHeckeRepOne : HeckeAlgOne →+* Module.End ℚ_[p] (RationalTateModule p J) :=
  (Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J)).toRingHom.comp (tateHeckeRepOne p J)

theorem rationalHeckeRepOne_apply (t : HeckeAlgOne) :
    rationalHeckeRepOne p J t = (tateHeckeRepOne p J t).baseChange ℚ_[p] :=
  rfl

theorem rationalHeckeRepOne_tmul (t : HeckeAlgOne) (a : ℚ_[p]) (x : TateModule p J) :
    rationalHeckeRepOne p J t (a ⊗ₜ x) = a ⊗ₜ tateHeckeRepOne p J t x :=
  rfl

def rationalHeckeAlgebraOne : Subalgebra ℚ_[p] (Module.End ℚ_[p] (RationalTateModule p J)) :=
  Algebra.adjoin ℚ_[p] (Set.range (rationalHeckeRepOne p J))

theorem rationalHeckeRepOne_mem_rationalHeckeAlgebraOne (t : HeckeAlgOne) :
    rationalHeckeRepOne p J t ∈ rationalHeckeAlgebraOne p J :=
  Algebra.subset_adjoin (Set.mem_range_self t)

def rationalDiamondOne (d : ℕ) : rationalHeckeAlgebraOne p J :=
  ⟨rationalHeckeRepOne p J (diamondGen d), rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J _⟩

@[simp] theorem coe_rationalDiamondOne (d : ℕ) :
    (rationalDiamondOne p J d : Module.End ℚ_[p] (RationalTateModule p J))
      = rationalHeckeRepOne p J (diamondGen d) := rfl

def rationalHeckeOne (ℓ : Nat.Primes) : rationalHeckeAlgebraOne p J :=
  ⟨rationalHeckeRepOne p J (heckeGenOne ℓ), rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J _⟩

@[simp] theorem coe_rationalHeckeOne (ℓ : Nat.Primes) :
    (rationalHeckeOne p J ℓ : Module.End ℚ_[p] (RationalTateModule p J))
      = rationalHeckeRepOne p J (heckeGenOne ℓ) := rfl

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
