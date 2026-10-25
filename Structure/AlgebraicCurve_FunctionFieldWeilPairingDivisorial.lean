import Structure.AlgebraicCurve_WeilDatum
import Structure.AlgebraicCurve_JacobianH1Autoduality
import Lemma.Scheme.PlaceEvaluationAlgebra

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Divisor


end Divisor

namespace WeilDatum

variable {n : ℕ}

private theorem isPrincipal_smul_left (d : WeilDatum K F n) :
    Divisor.IsPrincipal ((n : ℤ) • d.D₁) :=
  ⟨d.f₁, d.f₁_ne_zero, fun v => by rw [Finsupp.smul_apply, smul_eq_mul, d.ord_f₁ v]⟩

theorem isPrincipal_smul_right (d : WeilDatum K F n) :
    Divisor.IsPrincipal ((n : ℤ) • d.D₂) :=
  d.symm.isPrincipal_smul_left

theorem degree_D₁_eq_zero (d : WeilDatum K F n) [HasPrincipalDivisors K F] (hn : n ≠ 0) :
    Divisor.degree d.D₁ = 0 := by
  have h := Divisor.degree_eq_zero_of_isPrincipal d.isPrincipal_smul_left
  rw [map_zsmul, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn)

theorem degree_D₂_eq_zero (d : WeilDatum K F n) [HasPrincipalDivisors K F] (hn : n ≠ 0) :
    Divisor.degree d.D₂ = 0 :=
  d.symm.degree_D₁_eq_zero hn

end WeilDatum

namespace WeilDatum

variable {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]

def degZeroLeft (d : WeilDatum K F n) : Divisor.degZero (K := K) (F := F) :=
  ⟨d.D₁, Divisor.mem_degZero.mpr (d.degree_D₁_eq_zero (NeZero.ne n))⟩

def degZeroRight (d : WeilDatum K F n) : Divisor.degZero (K := K) (F := F) :=
  ⟨d.D₂, Divisor.mem_degZero.mpr (d.degree_D₂_eq_zero (NeZero.ne n))⟩

@[simp] theorem coe_degZeroLeft (d : WeilDatum K F n) :
    (d.degZeroLeft : Divisor K F) = d.D₁ := rfl

@[simp] theorem coe_degZeroRight (d : WeilDatum K F n) :
    (d.degZeroRight : Divisor K F) = d.D₂ := rfl

omit [NeZero n] [HasPrincipalDivisors K F] in

theorem mk_mem_torsion (D : Divisor.degZero (K := K) (F := F))
    (h : Divisor.IsPrincipal ((n : ℤ) • (D : Divisor K F))) :
    Pic0.mk D ∈ Pic0.torsion K F n := by
  rw [Pic0.mem_torsion]
  have h1 : (n : ℤ) • Pic0.mk D = Pic0.mk ((n : ℤ) • D) := by
    show (n : ℤ) • (QuotientAddGroup.mk D) = QuotientAddGroup.mk ((n : ℤ) • D)
    exact (QuotientAddGroup.mk_zsmul
      ((Divisor.principal (K := K) (F := F)).addSubgroupOf
        (Divisor.degZero (K := K) (F := F))) D (n : ℤ)).symm
  rw [h1]
  refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
  have hcoe : (((n : ℤ) • D : Divisor.degZero (K := K) (F := F)) : Divisor K F)
      = (n : ℤ) • (D : Divisor K F) := rfl
  show ((n : ℤ) • D : Divisor.degZero (K := K) (F := F)) ∈
    (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F))
  rw [AddSubgroup.mem_addSubgroupOf, hcoe]
  exact Divisor.mem_principal.mpr h

def classLeft (d : WeilDatum K F n) : Pic0.torsion K F n :=
  ⟨Pic0.mk d.degZeroLeft, mk_mem_torsion d.degZeroLeft (by
    rw [coe_degZeroLeft]; exact d.isPrincipal_smul_left)⟩

def classRight (d : WeilDatum K F n) : Pic0.torsion K F n :=
  ⟨Pic0.mk d.degZeroRight, mk_mem_torsion d.degZeroRight (by
    rw [coe_degZeroRight]; exact d.isPrincipal_smul_right)⟩


end WeilDatum

namespace WeilDatum

variable {n : ℕ} (d : WeilDatum K F n)


end WeilDatum

section GaloisAction

open scoped Pointwise

namespace Place

variable (σ : F ≃ₐ[K] F) (v : Place K F)


end Place

namespace Divisor

variable (σ : F ≃ₐ[K] F)


end Divisor

namespace WeilDatum

variable {n : ℕ} (σ : F ≃ₐ[K] F)


variable [NeZero n] [HasPrincipalDivisors K F]


end WeilDatum


end GaloisAction

namespace WeilDatum

variable {n : ℕ}


end WeilDatum

namespace WeilDatum

variable {n : ℕ} (d : WeilDatum K F n)


end WeilDatum

section Carrier

variable (K F) in

structure DivisorialWeilPairingData (n : ℕ) [NeZero n] [HasPrincipalDivisors K F] where

  pair : Pic0.torsion K F n → Pic0.torsion K F n → K

  compatible : ∀ d : WeilDatum K F n, pair d.classLeft d.classRight = d.pairing

  move : ∀ (x : Pic0.torsion K F n) (S : Finset (Place K F)),
    ∃ D : Divisor.degZero (K := K) (F := F),
      Pic0.mk D = (x : Pic0 K F) ∧
      (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
      (∀ v ∈ (D : Divisor K F).support, v ∉ S)

namespace DivisorialWeilPairingData

variable {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]
variable (e : DivisorialWeilPairingData K F n)

omit [NeZero n] [HasPrincipalDivisors K F] in


end DivisorialWeilPairingData

end Carrier

section Bridge

variable {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]

namespace DivisorialWeilPairingData

variable (e : DivisorialWeilPairingData K F n)


end DivisorialWeilPairingData

variable (K F) in


end Bridge

end AlgebraicCurve

/--
info: 'AlgebraicCurve.WeilDatum.classLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.WeilDatum.classLeft

/--
info: 'AlgebraicCurve.WeilDatum.galSmul_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.WeilDatum.galSmul_pairing

/--
info: 'AlgebraicCurve.WeilDatum.pairing_eq_of_addPrincipalLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.WeilDatum.pairing_eq_of_addPrincipalLeft

/--
info: 'AlgebraicCurve.DivisorialWeilPairingData.pair_add_left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.DivisorialWeilPairingData.pair_add_left

/--
info: 'AlgebraicCurve.DivisorialWeilPairingData.pair_pow_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.DivisorialWeilPairingData.pair_pow_eq_one

/--
info: 'AlgebraicCurve.DivisorialWeilPairingData.pair_self_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.DivisorialWeilPairingData.pair_self_eq_one

/--
info: 'AlgebraicCurve.DivisorialWeilPairingData.pair_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.DivisorialWeilPairingData.pair_smul

/--
info: 'AlgebraicCurve.DivisorialWeilPairingData.toWeilPairingData' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.DivisorialWeilPairingData.toWeilPairingData

/--
info: 'AlgebraicCurve.nonempty_weilPairingData_of_existsPerfectDivisorialWeilPairing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicCurve.nonempty_weilPairingData_of_existsPerfectDivisorialWeilPairing
