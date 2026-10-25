-- Carved from Lemma/Definitions/Def_ModularCurve_NodeDescentTower.lean: instance decls only.
import Mathlib
import Def.ModularCurve_NodeDescent
set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace NodeLocalized

open CharPReduction

variable (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ))

instance charZero_laurentSeries_algClosure : CharZero (LaurentSeries (AlgebraicClosure ℚ)) :=
  charZero_of_injective_ringHom (HahnSeries.C_injective (Γ := ℤ) (R := AlgebraicClosure ℚ))

instance charZero_fieldOver : CharZero (fieldOver N K) :=
  (fieldOver N K).subtype.charZero


instance algebraFieldOver : Algebra K (fieldOver N K) :=
  RingHom.toAlgebra
    { toFun := fun c => ⟨constSeries K.toSubalgebra.toSubring c, constSeries_mem_fieldOver N K c⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }


instance algebraFieldOverBar : Algebra (fieldOver N K) (modularFunctionFieldBar N) :=
  (Subring.inclusion (fieldOver_le_modularFunctionFieldBar N K)).toAlgebra


instance isScalarTower_fieldOver_bar_laurent :
    IsScalarTower (fieldOver N K) (modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ)) :=
  IsScalarTower.of_algebraMap_eq (R := fieldOver N K) (S := modularFunctionFieldBar N)
    (A := LaurentSeries (AlgebraicClosure ℚ)) (fun _ => rfl)

instance isScalarTower_K_fieldOver_bar :
    IsScalarTower K (fieldOver N K) (modularFunctionFieldBar N) :=
  IsScalarTower.of_algebraMap_eq (R := K) (S := fieldOver N K) (A := modularFunctionFieldBar N)
    (fun _ => Subtype.ext rfl)

section PrimeLevel

variable (q : ℕ) [Fact q.Prime]


instance algebra_isIntegral_fieldOver_bar :
    Algebra.IsIntegral (fieldOver (1 * q) K) (modularFunctionFieldBar (1 * q)) := by
  refine ⟨fun x => ?_⟩
  rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(fieldOver (1 * q) K)
      ↥(modularFunctionFieldBar (1 * q)) (LaurentSeries (AlgebraicClosure ℚ))) Subtype.val_injective]
  change IsIntegral (fieldOver (1 * q) K) (x : LaurentSeries (AlgebraicClosure ℚ))
  suffices h : ∀ y ∈ Subfield.closure
      (Set.range (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) ∪
        ⇑(coeffEmb (AlgebraicClosure ℚ)) '' (modularFunctionFieldFull (1 * q) : Set (LaurentSeries ℚ))),
      IsIntegral (fieldOver (1 * q) K) y from h _ (mem_laurentBaseChange_iff.mp x.2)
  intro y hy
  induction hy using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨z, hz, rfl⟩
      · exact isIntegral_fieldOver_algebraMap_laurent K q c
      · exact isIntegral_algebraMap (R := ↥(fieldOver (1 * q) K))
          (x := ⟨_, coeffEmb_mem_fieldOver_of_mem_full K q hz⟩)
  | one => exact isIntegral_one
  | add y z _ _ hy hz => exact hy.add hz
  | neg y _ hy => exact hy.neg
  | inv y _ hy => exact hy.inv
  | mul y z _ _ hy hz => exact hy.mul hz

end PrimeLevel

end NodeLocalized
end ModularCurve

end
