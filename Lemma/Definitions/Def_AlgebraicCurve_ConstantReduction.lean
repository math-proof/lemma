import Mathlib
import Lemma.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Lemma.Definitions.Def_AlgebraicCurve_Repartitions

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]

structure ConstantReduction where

  integers : ValuationSubring F

  residue : integers →+* Fbar

  placeMap : Place L F → Place (ResidueField A) Fbar

  algebraMap_mem_iff : ∀ x : L, algebraMap L F x ∈ integers ↔ x ∈ A

  residue_surjective : Function.Surjective residue

  ker_residue : RingHom.ker residue = maximalIdeal integers

  residue_algebraMap : ∀ a : A,
    residue ⟨algebraMap L F a, (algebraMap_mem_iff a).mpr a.2⟩ =
      algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a)

  exists_smul_mem : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ integers, residue ⟨c • f, h⟩ ≠ 0

  deg_placeMap : ∀ P, (placeMap P).deg = P.deg

  mapDomain_placeMap : ∀ f : integers, residue f ≠ 0 → ∀ D : Divisor L F,
    (∀ P, D P = P.ord (f : F)) → ∀ Q, Finsupp.mapDomain placeMap D Q = Q.ord (residue f)

namespace ConstantReduction

variable {A F Fbar}

set_option linter.unusedVariables false in

def IsGood (R : ConstantReduction A F Fbar) : Prop :=
  genusFF (ResidueField A) Fbar = genusFF L F

theorem isGood_iff (R : ConstantReduction A F Fbar) :
    R.IsGood ↔ genusFF (ResidueField A) Fbar = genusFF L F :=
  Iff.rfl

variable (R : ConstantReduction A F Fbar)

theorem ord_algebraMap (P : Place L F) {c : L} (hc : c ≠ 0) : P.ord (algebraMap L F c) = 0 := by
  have hu : IsUnit (⟨algebraMap L F c, P.algebraMap_mem' c⟩ : P.toValuationSubring) :=
    ⟨⟨⟨algebraMap L F c, P.algebraMap_mem' c⟩, ⟨algebraMap L F c⁻¹, P.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simpa using mul_inv_cancel₀ ((map_ne_zero (algebraMap L F)).mpr hc)),
      Subtype.ext (by simpa using inv_mul_cancel₀ ((map_ne_zero (algebraMap L F)).mpr hc))⟩, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have := P.ord_coe_unit u
  rwa [hu] at this

theorem ord_smul (P : Place L F) {c : L} (hc : c ≠ 0) (f : F) : P.ord (c • f) = P.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [Algebra.smul_def, P.ord_mul ((map_ne_zero _).mpr hc) hf, ord_algebraMap P hc, zero_add]

theorem mapDomain_mem_principal {D : Divisor L F}
    (hD : D ∈ Divisor.principal (K := L) (F := F)) :
    Finsupp.mapDomain R.placeMap D ∈ Divisor.principal (K := ResidueField A) (F := Fbar) := by
  obtain ⟨f, hf0, hDf⟩ := hD
  obtain ⟨c, hc, hres⟩ := R.exists_smul_mem f hf0
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : L) • f, hc⟩ : R.integers) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]
  exact ⟨R.residue ⟨c • f, hc⟩, hres, fun Q =>
    R.mapDomain_placeMap ⟨c • f, hc⟩ hres D (fun P => by rw [hDf P]; exact (ord_smul P hc0 f).symm) Q⟩

theorem degree_mapDomain (D : Divisor L F) :
    Divisor.degree (Finsupp.mapDomain R.placeMap D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add P n D _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single,
      Divisor.degree_single, Divisor.degree_single, R.deg_placeMap]

theorem mapDomain_mem_degZero {D : Divisor L F}
    (hD : D ∈ Divisor.degZero (K := L) (F := F)) :
    Finsupp.mapDomain R.placeMap D ∈ Divisor.degZero (K := ResidueField A) (F := Fbar) := by
  rw [Divisor.mem_degZero] at hD ⊢
  rw [R.degree_mapDomain, hD]

def divMap : Divisor L F →+ Divisor (ResidueField A) Fbar :=
  Finsupp.mapDomain.addMonoidHom R.placeMap

@[simp]
theorem divMap_apply (D : Divisor L F) : R.divMap D = Finsupp.mapDomain R.placeMap D := rfl

def degZeroMap :
    Divisor.degZero (K := L) (F := F) →+ Divisor.degZero (K := ResidueField A) (F := Fbar) :=
  (R.divMap.domRestrict (Divisor.degZero (K := L) (F := F))).codRestrict _ fun D => R.mapDomain_mem_degZero D.2

@[simp]
theorem coe_degZeroMap (D : Divisor.degZero (K := L) (F := F)) :
    (R.degZeroMap D : Divisor (ResidueField A) Fbar) = Finsupp.mapDomain R.placeMap (D : Divisor L F) :=
  rfl

def pic0Map : Pic0 L F →+ Pic0 (ResidueField A) Fbar :=
  QuotientAddGroup.map _ _ R.degZeroMap (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact R.mapDomain_mem_principal hD)

theorem pic0Map_mk (D : Divisor.degZero (K := L) (F := F)) :
    R.pic0Map (Pic0.mk D) = Pic0.mk (R.degZeroMap D) :=
  rfl

end ConstantReduction

end AlgebraicCurve

end
