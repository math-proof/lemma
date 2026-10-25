-- Carved from Lemma/Definitions/Def_NumberField_LevelArithmeticModP.lean: instance decls only.
import Mathlib
import Lemma.NumberField.SUnitsModule
import Instance.ExtEndgame_ProductionDatum
import Lemma.ClassGroup.GaloisAction
import Instance.Compat_Mathlib430
import Lemma.NumberField.LevelArithmeticModP

set_option autoImplicit false

noncomputable section

open CategoryTheory IsDedekindDomain
open scoped Pointwise NumberField nonZeroDivisors

namespace NumberField.LevelArith

section Bridge

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)

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

scoped instance instModuleZModQuot {V : Type} [AddCommGroup V] {iV : Module k V} (p : ℕ) :
    Module (ZMod p) (V ⧸ ((p : k) • (⊤ : Submodule k V))) :=
  AddCommGroup.zmodModule (nsmul_quot_eq_zero p)

scoped instance instModuleZModTorsion {V : Type} [AddCommGroup V] {iV : Module k V} (p : ℕ) :
    Module (ZMod p) ↥(Submodule.torsionBy k V (p : k)) :=
  AddCommGroup.zmodModule (nsmul_torsionBy_eq_zero p)

end ModP

section ClassGroups

variable (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F]

scoped instance instMulDistribMulActionClassGroup : MulDistribMulAction (F ≃ₐ[E] F) (ClassGroup (𝓞 F)) :=
  MulDistribMulAction.compHom _ (classGroupAut E F)

end ClassGroups


end NumberField.LevelArith

end
