import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Ring.Subring.Pointwise
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Bezout
import Structure.AlgebraicCurve_Place
import Instance.AlgebraicCurve_DivisorClassGroup
import Abbrev.AlgebraicCurve_DivisorClassGroup

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Divisor

variable {K F}

def degree : Divisor K F →+ ℤ :=
  Finsupp.liftAddHom fun v => AddMonoidHom.mulRight (v.deg : ℤ)

@[simp]
theorem degree_single (v : Place K F) (n : ℤ) :
    degree (Finsupp.single v n) = n * v.deg := by
  simp [degree]

def degZero : AddSubgroup (Divisor K F) := degree.ker

theorem mem_degZero {D : Divisor K F} : D ∈ degZero (K := K) (F := F) ↔ degree D = 0 :=
  Iff.rfl

def IsPrincipal (D : Divisor K F) : Prop := ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, D v = v.ord f

def principal : AddSubgroup (Divisor K F) where
  carrier := {D | IsPrincipal D}
  zero_mem' := ⟨1, one_ne_zero, fun v => by simp⟩
  add_mem' := by
    rintro D E ⟨f, hf, hD⟩ ⟨g, hg, hE⟩
    exact ⟨f * g, mul_ne_zero hf hg, fun v => by
      rw [Finsupp.add_apply, hD v, hE v, v.ord_mul hf hg]⟩
  neg_mem' := by
    rintro D ⟨f, hf, hD⟩
    exact ⟨f⁻¹, inv_ne_zero hf, fun v => by
      rw [Finsupp.neg_apply, hD v, v.ord_inv]⟩

theorem mem_principal {D : Divisor K F} :
    D ∈ principal (K := K) (F := F) ↔ IsPrincipal D := Iff.rfl

end Divisor

class HasPrincipalDivisors : Prop where
  exists_divisor : ∀ f : F, f ≠ 0 → ∃ D : Divisor K F,
    (∀ v : Place K F, D v = v.ord f) ∧ Divisor.degree D = 0

abbrev Pic : Type _ := Divisor K F ⧸ Divisor.principal (K := K) (F := F)

abbrev Pic0 : Type _ :=
  Divisor.degZero (K := K) (F := F) ⧸
    (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F))

namespace Pic0

variable {K F}

def mk (D : Divisor.degZero (K := K) (F := F)) : Pic0 K F := QuotientAddGroup.mk D

theorem mk_surjective : Function.Surjective (mk (K := K) (F := F)) :=
  QuotientAddGroup.mk_surjective

@[simp]
theorem mk_add (D E : Divisor.degZero (K := K) (F := F)) : mk (D + E) = mk D + mk E := rfl

@[simp]
theorem mk_zero : mk (0 : Divisor.degZero (K := K) (F := F)) = 0 := rfl

variable (K F) in

def torsion (n : ℕ) : AddSubgroup (Pic0 K F) :=
  (Submodule.torsionBy ℤ (Pic0 K F) (n : ℤ)).toAddSubgroup

theorem mem_torsion {n : ℕ} {x : Pic0 K F} : x ∈ torsion K F n ↔ (n : ℤ) • x = 0 :=
  Submodule.mem_torsionBy_iff _ _

end Pic0

def AbelJacobiCard (p : ℕ) (g : ℕ) : Prop :=
  ∀ n : ℕ, Nat.card (Pic0.torsion K F (p ^ n)) = p ^ (2 * g * n)

namespace Place

open scoped Pointwise

variable {K F}
variable (σ : F ≃ₐ[K] F)

def smulRingEquiv (A : ValuationSubring F) : A ≃+* (σ • A : ValuationSubring F) where
  toFun x := ⟨σ x, by
    simpa [AlgEquiv.smul_def] using
      ValuationSubring.smul_mem_pointwise_smul σ (x : F) A x.2⟩
  invFun y := ⟨σ.symm y, by
    have := (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem (g := σ)
      (S := A) (x := (y : F))).mp y.2
    simpa [AlgEquiv.smul_def, AlgEquiv.aut_inv] using this⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

@[simp]
theorem coe_smulRingEquiv_apply (A : ValuationSubring F) (x : A) :
    ((smulRingEquiv σ A x : (σ • A : ValuationSubring F)) : F) = σ x := rfl

theorem _root_.ValuationSubring.pointwise_smul_top :
    σ • (⊤ : ValuationSubring F) = ⊤ := by
  ext x
  simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact ⟨fun _ => ValuationSubring.mem_top x, fun _ => ValuationSubring.mem_top _⟩

variable (v : Place K F)

@[simp]
theorem smul_toValuationSubring : (σ • v).toValuationSubring = σ • v.toValuationSubring := rfl

theorem ord_smul (f : F) : (σ • v).ord (σ f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ

  set n := v.ord f with hn

  set e := smulRingEquiv σ v.toValuationSubring with he
  have hπ' : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  have hu' : IsUnit (e (u : v.toValuationSubring)) := u.isUnit.map e
  have hcoeu : ((hu'.unit : (σ • v).toValuationSubring) : F)
      = σ ((u : v.toValuationSubring) : F) := by
    rw [IsUnit.unit_spec]
    rfl
  have hcoeπ : ((e π : (σ • v).toValuationSubring) : F) = σ (π : F) := rfl
  have key : σ f = ((hu'.unit : (σ • v).toValuationSubring) : F)
      * (((e π : (σ • v).toValuationSubring) : F) ^ n) := by
    rw [hcoeu, hcoeπ, hu, map_mul, map_zpow₀]
  rw [key, (σ • v).ord_unit_smul_zpow hu'.unit hπ' n]

def smulResidueAlgEquiv : v.ResidueField ≃ₐ[K] (σ • v).ResidueField :=
  AlgEquiv.ofRingEquiv (f := IsLocalRing.ResidueField.mapEquiv
      (smulRingEquiv σ v.toValuationSubring)) <| fun a => by
    have h3 : (smulRingEquiv σ v.toValuationSubring) (algebraMap K v.toValuationSubring a)
        = algebraMap K (σ • v).toValuationSubring a := by
      ext
      rw [coe_smulRingEquiv_apply, coe_algebraMap, σ.commutes]
      rfl
    show IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _) = IsLocalRing.residue _ _
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    exact congrArg _ h3

@[simp]
theorem deg_smul : (σ • v).deg = v.deg :=
  ((smulResidueAlgEquiv σ v).toLinearEquiv.finrank_eq).symm

end Place

namespace Divisor

open scoped Pointwise

variable {K F}

theorem smul_def (σ : F ≃ₐ[K] F) (D : Divisor K F) :
    σ • D = Finsupp.mapDomain (σ • ·) D := rfl

@[simp]
theorem smul_single (σ : F ≃ₐ[K] F) (v : Place K F) (n : ℤ) :
    σ • Finsupp.single v n = Finsupp.single (σ • v) n := by
  rw [smul_def, Finsupp.mapDomain_single]

theorem smul_apply_smul (σ : F ≃ₐ[K] F) (D : Divisor K F) (v : Place K F) :
    (σ • D) (σ • v) = D v := by
  rw [smul_def]
  exact Finsupp.mapDomain_apply_of_injective (MulAction.injective σ) D v

theorem smul_apply (σ : F ≃ₐ[K] F) (D : Divisor K F) (w : Place K F) :
    (σ • D) w = D (σ⁻¹ • w) := by
  have : (σ • D) (σ • (σ⁻¹ • w)) = D (σ⁻¹ • w) := smul_apply_smul σ D (σ⁻¹ • w)
  rwa [smul_inv_smul] at this

@[simp]
theorem degree_smul (σ : F ≃ₐ[K] F) (D : Divisor K F) : degree (σ • D) = degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
      rw [smul_add, map_add, map_add, ih, smul_single, degree_single, degree_single,
        Place.deg_smul]

theorem smul_mem_degZero (σ : F ≃ₐ[K] F) {D : Divisor K F}
    (hD : D ∈ degZero (K := K) (F := F)) : σ • D ∈ degZero (K := K) (F := F) := by
  rwa [mem_degZero, degree_smul]

theorem smul_mem_principal (σ : F ≃ₐ[K] F) {D : Divisor K F}
    (hD : D ∈ principal (K := K) (F := F)) : σ • D ∈ principal (K := K) (F := F) := by
  obtain ⟨f, hf, hD⟩ := hD
  refine ⟨σ f, by simpa using hf, fun w => ?_⟩
  rw [smul_apply, hD (σ⁻¹ • w)]
  have h := Place.ord_smul σ (σ⁻¹ • w) f
  rw [smul_inv_smul] at h
  exact h.symm

end Divisor

namespace Pic0

open scoped Pointwise

variable {K F}

def degZeroSMulHom (σ : F ≃ₐ[K] F) :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
  ((DistribSMul.toAddMonoidHom (Divisor K F) σ).domRestrict
    (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => Divisor.smul_mem_degZero σ D.2)

@[simp]
theorem coe_degZeroSMulHom (σ : F ≃ₐ[K] F) (D : Divisor.degZero (K := K) (F := F)) :
    (degZeroSMulHom σ D : Divisor K F) = σ • (D : Divisor K F) := rfl

theorem smul_mk (σ : F ≃ₐ[K] F) (D : Divisor.degZero (K := K) (F := F)) :
    σ • (mk D) = mk (degZeroSMulHom σ D) := rfl

end Pic0

namespace Place

variable {K F}
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

open IsDedekindDomain.HeightOneSpectrum in

theorem isPrincipalIdealRing_valuationSubring (w : HeightOneSpectrum R) :
    IsPrincipalIdealRing ((w.valuation F).valuationSubring) := by
  rw [show (w.valuation F).valuationSubring = valuationSubringAtPrime F w from
    (valuationSubringAtPrime_eq_valuationSubring (K := F) w).symm]

  infer_instance

open IsDedekindDomain.HeightOneSpectrum in

def ofHeightOneSpectrum [Algebra K R] [IsScalarTower K R F] (w : HeightOneSpectrum R) :
    Place K F where
  toValuationSubring := (w.valuation F).valuationSubring
  algebraMap_mem' := fun a => by
    rw [Valuation.mem_valuationSubring_iff, IsScalarTower.algebraMap_apply K R F]
    exact w.valuation_le_one (algebraMap K R a)
  ne_top' := by
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  isPrincipalIdealRing' := isPrincipalIdealRing_valuationSubring w

@[simp]
theorem ofHeightOneSpectrum_toValuationSubring [Algebra K R] [IsScalarTower K R F]
    (w : HeightOneSpectrum R) :
    (ofHeightOneSpectrum (K := K) w).toValuationSubring = (w.valuation F).valuationSubring :=
  rfl

end Place

end AlgebraicCurve
