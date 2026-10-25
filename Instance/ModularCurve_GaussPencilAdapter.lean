-- Carved from Lemma/Definitions/Def_ModularCurve_GaussPencilAdapter.lean: instance decls only.
import Mathlib

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

section InstanceShortcuts
open ModularCurve

noncomputable instance (priority := high) instFieldLaurentSeriesAlgClosureRat :
    Field (LaurentSeries (AlgebraicClosure ℚ)) := inferInstance
noncomputable instance (priority := high) instAlgebraLaurentSeriesAlgClosureRat :
    Algebra (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) := inferInstance
noncomputable instance (priority := high) instFieldModularFunctionFieldBar (N : ℕ) :
    Field ↥(modularFunctionFieldBar N) := inferInstance
noncomputable instance (priority := high) instAlgebraModularFunctionFieldBar (N : ℕ) :
    Algebra (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := inferInstance
noncomputable instance (priority := high) instModuleModularFunctionFieldBar (N : ℕ) :
    Module (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := inferInstance
noncomputable instance (priority := high) instCommRingModularFunctionFieldBar (N : ℕ) :
    CommRing ↥(modularFunctionFieldBar N) := inferInstance
noncomputable instance (priority := high) instFieldModularFunctionFieldC (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Field ↥(modularFunctionFieldC k N) := inferInstance
noncomputable instance (priority := high) instAlgebraModularFunctionFieldC (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Algebra k ↥(modularFunctionFieldC k N) := inferInstance
noncomputable instance (priority := high) instFieldModularFunctionFieldFullC (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Field ↥(modularFunctionFieldFullC k N) := inferInstance
noncomputable instance (priority := high) instAlgebraModularFunctionFieldFullC (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Algebra k ↥(modularFunctionFieldFullC k N) := inferInstance
noncomputable instance (priority := high) instFieldLaurentSeries' (k : Type*) [Field k] :
    Field (LaurentSeries k) := inferInstance

end InstanceShortcuts

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve.PlaceSpecialization.LevelOneProlongationPair

section Core

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
  {K₁ : Type*} [Field K₁] [Algebra (AlgebraicClosure ℚ) K₁]
  [Algebra K₁ (modularFunctionFieldBar (1 * q))]
  [IsScalarTower (AlgebraicClosure ℚ) K₁ (modularFunctionFieldBar (1 * q))]

variable (R : LevelOneProlongationPair P)


noncomputable instance algGaussBase : Algebra (R.gaussBase K₁) (modularFunctionFieldBar (1 * q)) :=
  ((algebraMap K₁ (modularFunctionFieldBar (1 * q))).comp (algebraMap (R.gaussBase K₁) K₁)).toAlgebra

instance isScalarTower_gaussBase : IsScalarTower (R.gaussBase K₁) K₁ (modularFunctionFieldBar (1 * q)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl


noncomputable instance : Field R.ResOne := inferInstanceAs (Field ↥(modularFunctionFieldFullC (ResidueField A) 1))
noncomputable instance : Field R.ResTwo := inferInstanceAs (Field ↥(modularFunctionFieldFullC (ResidueField A) 1))


noncomputable instance : Algebra (R.gaussBase K₁) R.ResOne := (R.resBase₁ K₁).toAlgebra


instance isLocalHom_resBase₁ : IsLocalHom (R.resBase₁ K₁) := by
  refine ⟨fun x hx => ?_⟩
  have hne : R.R₁.residue (R.toIntegers₁ K₁ x) ≠ 0 := hx.ne_zero
  exact R.isUnit_of_isUnit_toIntegers (R.toIntegers₁ K₁) R.coe_toIntegers₁
    (fun y hy => (R.mem_gaussBase_iff y).mpr hy) x (R.R₁.isUnit_of_residue_ne_zero hne)

noncomputable instance : Algebra (ResidueField (R.gaussBase K₁)) R.ResOne :=
  (IsLocalRing.ResidueField.lift (R.resBase₁ K₁)).toAlgebra

instance isScalarTower_resOne : IsScalarTower (R.gaussBase K₁) (ResidueField (R.gaussBase K₁)) R.ResOne :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
    exact (IsLocalRing.ResidueField.lift_residue_apply _ x).symm


instance isLocalHom_constToGaussBase : IsLocalHom (R.constToGaussBase K₁) := by
  refine ⟨fun a ha => ?_⟩
  have h1 : (R.gaussBase K₁).valuation (algebraMap (AlgebraicClosure ℚ) K₁ a) = 1 :=
    ((R.gaussBase K₁).valuation_eq_one_iff (R.constToGaussBase K₁ a)).mp ha
  have ha0 : (a : AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero] at h1
    exact zero_ne_one h1
  have hinv : algebraMap (AlgebraicClosure ℚ) K₁ ((a : AlgebraicClosure ℚ)⁻¹) ∈ R.gaussBase K₁ := by
    rw [← (R.gaussBase K₁).valuation_le_one_iff, map_inv₀, map_inv₀, h1, inv_one]
  have hinvA : (a : AlgebraicClosure ℚ)⁻¹ ∈ A := (R.algebraMap_mem_gaussBase_iff _).mp hinv
  exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinvA⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

noncomputable instance algResidueConst : Algebra (ResidueField A) (ResidueField (R.gaussBase K₁)) :=
  (IsLocalRing.ResidueField.map (R.constToGaussBase K₁)).toAlgebra


noncomputable instance : Algebra (R.gaussBase K₁) R.ResTwo := (R.resBase₂ K₁).toAlgebra

instance isLocalHom_resBase₂ : IsLocalHom (R.resBase₂ K₁) := by
  refine ⟨fun x hx => ?_⟩
  have hne : R.R₂.residue (R.toIntegers₂ K₁ x) ≠ 0 := hx.ne_zero
  exact R.isUnit_of_isUnit_toIntegers (R.toIntegers₂ K₁) R.coe_toIntegers₂
    (fun y hy => R.mem_gaussBase_of_algebraMap_mem_integers₂ y hy) x (R.R₂.isUnit_of_residue_ne_zero hne)

noncomputable instance : Algebra (ResidueField (R.gaussBase K₁)) R.ResTwo :=
  (IsLocalRing.ResidueField.lift (R.resBase₂ K₁)).toAlgebra

instance isScalarTower_resTwo : IsScalarTower (R.gaussBase K₁) (ResidueField (R.gaussBase K₁)) R.ResTwo :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
    exact (IsLocalRing.ResidueField.lift_residue_apply _ x).symm


end Core

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair

end
