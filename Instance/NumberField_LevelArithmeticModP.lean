-- Carved from Lemma/Definitions/Def_NumberField_LevelArithmeticModP.lean: instance decls only.
import Mathlib
import Abbrev.NumberField_LevelArithmeticModP
import Lemma.ClassGroup.GaloisAction

set_option autoImplicit false

noncomputable section

open CategoryTheory IsDedekindDomain
open scoped Pointwise NumberField nonZeroDivisors

namespace NumberField.LevelArith

section Bridge

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)

private def levelFieldEquiv : ↥L ≃+* ↥(levelField K L hKL) where
  toFun x := ⟨(x : AlgebraicClosure ℚ), (IntermediateField.mem_extendScalars hKL).2 x.2⟩
  invFun y := ⟨(y : AlgebraicClosure ℚ), (IntermediateField.mem_extendScalars hKL).1 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

scoped instance instFiniteDimensionalLevelField [FiniteDimensional ℚ ↥L] : FiniteDimensional ℚ ↥(levelField K L hKL) :=
  LinearEquiv.finiteDimensional ((levelFieldEquiv K L hKL).toAddEquiv.toLinearEquiv fun c x => map_rat_smul _ c x)

scoped instance instNumberFieldLevelField [FiniteDimensional ℚ ↥L] : NumberField ↥(levelField K L hKL) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

scoped instance instNumberFieldBase [FiniteDimensional ℚ ↥K] : NumberField ↥K where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

end Bridge

section ModP

variable {k : Type} [CommRing k] {G : Type} [Group G]

private theorem nsmul_quot_eq_zero {V : Type} [AddCommGroup V] {iV : Module k V} (p : ℕ)
    (x : V ⧸ ((p : k) • (⊤ : Submodule k V))) : p • x = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    ← Nat.cast_smul_eq_nsmul k]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

private theorem nsmul_torsionBy_eq_zero {V : Type} [AddCommGroup V] {iV : Module k V} (p : ℕ)
    (x : ↥(Submodule.torsionBy k V (p : k))) : p • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul k]
  exact Subtype.ext ((Submodule.mem_torsionBy_iff (p : k) (x : V)).1 x.2)

scoped instance instModuleZModQuot {V : Type} [AddCommGroup V] {iV : Module k V} (p : ℕ) :
    Module (ZMod p) (V ⧸ ((p : k) • (⊤ : Submodule k V))) :=
  AddCommGroup.zmodModule (nsmul_quot_eq_zero p)

scoped instance instModuleZModTorsion {V : Type} [AddCommGroup V] {iV : Module k V} (p : ℕ) :
    Module (ZMod p) ↥(Submodule.torsionBy k V (p : k)) :=
  AddCommGroup.zmodModule (nsmul_torsionBy_eq_zero p)

end ModP

section ClassGroups

variable (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F]

private def classGroupAut : (F ≃ₐ[E] F) →* MulAut (ClassGroup (𝓞 F)) where
  toFun σ := ClassGroup.mulEquiv (ringOfIntegersAut E F σ)
  map_one' := MulEquiv.ext fun C => by
    change ClassGroup.mulEquiv (ringOfIntegersAut E F 1) C = C
    have : ringOfIntegersAut E F 1 = RingEquiv.refl _ := RingEquiv.ext fun _ => rfl
    rw [this, ClassGroup.mulEquiv_refl_apply]
  map_mul' σ τ := MulEquiv.ext fun C => by
    change ClassGroup.mulEquiv (ringOfIntegersAut E F (σ * τ)) C =
      ClassGroup.mulEquiv (ringOfIntegersAut E F σ) (ClassGroup.mulEquiv (ringOfIntegersAut E F τ) C)
    have : ringOfIntegersAut E F (σ * τ) =
        (ringOfIntegersAut E F τ).trans (ringOfIntegersAut E F σ) :=
      RingEquiv.ext fun _ => rfl
    rw [this, ClassGroup.mulEquiv_trans_apply]

scoped instance instMulDistribMulActionClassGroup : MulDistribMulAction (F ≃ₐ[E] F) (ClassGroup (𝓞 F)) :=
  MulDistribMulAction.compHom _ (classGroupAut E F)

end ClassGroups


end NumberField.LevelArith

end
