module

public import Theorem.LaurentSeries.X1HeckeOperator
public import Theorem.UpperHalfPlane.X1Diamond
public import Theorem.WeierstrassCurve.JZeroTateModule
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Abbrev.ModularCurve_X1HeckeModule

public noncomputable section

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace ModularCurve

open AlgebraicCurve


@[simp] public theorem aeval_heckeGenOne {A : Type*} [CommSemiring A] [Algebra ℤ A]
    (a : Nat.Primes ⊕ ℕ → A) (ℓ : Nat.Primes) :
    MvPolynomial.aeval a (heckeGenOne ℓ) = a (Sum.inl ℓ) :=
  MvPolynomial.aeval_X a _


@[simp] public theorem aeval_diamondGen {A : Type*} [CommSemiring A] [Algebra ℤ A]
    (a : Nat.Primes ⊕ ℕ → A) (d : ℕ) :
    MvPolynomial.aeval a (diamondGen d) = a (Sum.inr d) :=
  MvPolynomial.aeval_X a _

section Operators

variable (M : ℕ)


public theorem heckeOperatorOneBar_apply (ℓ : Nat.Primes) (x : JOne M) :
    heckeOperatorOneBar M ℓ x =
      (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ x) :=
  rfl


@[simp] public theorem heckeDiamondGenBar_inl (ℓ : Nat.Primes) :
    heckeDiamondGenBar M (Sum.inl ℓ) = heckeOperatorOneBar M ℓ := rfl


@[simp] public theorem heckeDiamondGenBar_inr (d : ℕ) :
    heckeDiamondGenBar M (Sum.inr d) = diamondOneBar M d := rfl


public theorem isMulCommutative_adjoin_heckeDiamondGenBar (h : HeckeDiamondCommuteBar M) :
    IsMulCommutative (Algebra.adjoin ℤ (Set.range (heckeDiamondGenBar M))) :=
  Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact h i j)

open scoped IsMulCommutative in


public theorem heckeEvalOneBar_apply (h : HeckeDiamondCommuteBar M) (t : HeckeAlgOne) :
    heckeEvalOneBar h t = (heckeEvalOneBarAux h t : Module.End ℤ (JOne M)) :=
  rfl

set_option synthInstance.maxHeartbeats 400000 in
open scoped IsMulCommutative in

public theorem heckeEvalOneBarAux_X (h : HeckeDiamondCommuteBar M) (i : Nat.Primes ⊕ ℕ) :
    heckeEvalOneBarAux h (MvPolynomial.X i) =
      ⟨heckeDiamondGenBar M i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ :=
  haveI := isMulCommutative_adjoin_heckeDiamondGenBar h
  MvPolynomial.aeval_X _ i


public theorem heckeEvalOneBar_X (h : HeckeDiamondCommuteBar M) (i : Nat.Primes ⊕ ℕ) :
    heckeEvalOneBar h (MvPolynomial.X i) = heckeDiamondGenBar M i := by
  rw [heckeEvalOneBar_apply, heckeEvalOneBarAux_X]


public theorem heckeEvalOneBar_heckeGenOne (h : HeckeDiamondCommuteBar M) (ℓ : Nat.Primes) :
    heckeEvalOneBar h (heckeGenOne ℓ) = heckeOperatorOneBar M ℓ :=
  heckeEvalOneBar_X h (Sum.inl ℓ)


public theorem heckeEvalOneBar_diamondGen (h : HeckeDiamondCommuteBar M) (d : ℕ) :
    heckeEvalOneBar h (diamondGen d) = diamondOneBar M d :=
  heckeEvalOneBar_X h (Sum.inr d)


public theorem heckeEvalOneBar_C (h : HeckeDiamondCommuteBar M) (a : ℤ) :
    heckeEvalOneBar h (MvPolynomial.C a) = (a : Module.End ℤ (JOne M)) := by
  rw [← MvPolynomial.algebraMap_eq, eq_intCast, map_intCast]

end Eval

section TheModule

variable (M : ℕ)

open Classical in


public theorem heckeModuleOneBar_smul_def (h : HeckeDiamondCommuteBar M) (t : HeckeAlgOne) (x : JOne M) :
    (letI := heckeModuleOneBar M; t • x) = heckeEvalOneBar h t x := by
  have e : heckeModuleOneBar M = Module.compHom (JOne M) (heckeEvalOneBar h) := dif_pos h
  rw [e]
  rfl


public theorem heckeModuleOneBar_heckeGenOne_smul (h : HeckeDiamondCommuteBar M) (ℓ : Nat.Primes)
    (x : JOne M) : (letI := heckeModuleOneBar M; heckeGenOne ℓ • x) = heckeOperatorOneBar M ℓ x := by
  rw [heckeModuleOneBar_smul_def h, heckeEvalOneBar_heckeGenOne]


public theorem heckeModuleOneBar_diamondGen_smul (h : HeckeDiamondCommuteBar M) (d : ℕ)
    (x : JOne M) : (letI := heckeModuleOneBar M; diamondGen d • x) = diamondOneBar M d x := by
  rw [heckeModuleOneBar_smul_def h, heckeEvalOneBar_diamondGen]


public theorem heckeModuleOneBar_smul_of_not (h : ¬ HeckeDiamondCommuteBar M) (t : HeckeAlgOne) (x : JOne M) :
    (letI := heckeModuleOneBar M; t • x) = MvPolynomial.constantCoeff t • x := by
  have e : heckeModuleOneBar M =
      Module.compHom (JOne M)
        (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes ⊕ ℕ → ℤ)) :=
    dif_neg h
  rw [e]
  show (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes ⊕ ℕ → ℤ) t) • x = _
  rw [MvPolynomial.eval₂Hom_zero_apply, eq_intCast, Int.cast_id]


public theorem heckeModuleOneBar_X_smul_of_not (h : ¬ HeckeDiamondCommuteBar M) (i : Nat.Primes ⊕ ℕ)
    (x : JOne M) : (letI := heckeModuleOneBar M; (MvPolynomial.X i : HeckeAlgOne) • x) = 0 := by
  rw [heckeModuleOneBar_smul_of_not h, MvPolynomial.constantCoeff_X, zero_zsmul]


public theorem heckeModuleOneBar_C_smul (a : ℤ) (x : JOne M) :
    (letI := heckeModuleOneBar M; (MvPolynomial.C a : HeckeAlgOne) • x) = a • x := by
  by_cases h : HeckeDiamondCommuteBar M
  · rw [heckeModuleOneBar_smul_def h, heckeEvalOneBar_C, Module.End.intCast_apply]
  · rw [heckeModuleOneBar_smul_of_not h, MvPolynomial.constantCoeff_C]

end TheModule

section Integral

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlgOne J]


public theorem tateHeckeRepOne_apply (t : HeckeAlgOne) :
    tateHeckeRepOne p J t = TateModule.rep p J HeckeAlgOne t :=
  rfl


public theorem coe_tateHeckeRepOne_apply_apply (t : HeckeAlgOne) (x : TateModule p J) (n : ℕ) :
    ((tateHeckeRepOne p J t x : TateModule p J) : ℕ → J) n = t • (x : ℕ → J) n :=
  rfl

end Integral

section Rational

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlgOne J]


public theorem rationalHeckeRepOne_apply (t : HeckeAlgOne) :
    rationalHeckeRepOne p J t = (tateHeckeRepOne p J t).baseChange ℚ_[p] :=
  rfl


public theorem rationalHeckeRepOne_tmul (t : HeckeAlgOne) (a : ℚ_[p]) (x : TateModule p J) :
    rationalHeckeRepOne p J t (a ⊗ₜ x) = a ⊗ₜ tateHeckeRepOne p J t x :=
  rfl


public theorem rationalHeckeRepOne_mem_rationalHeckeAlgebraOne (t : HeckeAlgOne) :
    rationalHeckeRepOne p J t ∈ rationalHeckeAlgebraOne p J :=
  Algebra.subset_adjoin (Set.mem_range_self t)


@[simp] public theorem coe_rationalDiamondOne (d : ℕ) :
    (rationalDiamondOne p J d : Module.End ℚ_[p] (RationalTateModule p J))
      = rationalHeckeRepOne p J (diamondGen d) := rfl


@[simp] public theorem coe_rationalHeckeOne (ℓ : Nat.Primes) :
    (rationalHeckeOne p J ℓ : Module.End ℚ_[p] (RationalTateModule p J))
      = rationalHeckeRepOne p J (heckeGenOne ℓ) := rfl

end Rational

section Predicate

variable {K L : Type} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlgOne J]
  [DistribMulAction (L ≃ₐ[K] L) J]

