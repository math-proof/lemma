import Mathlib
import Lemma.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Def.AlgebraicCurve_PlaceEvaluation

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)


theorem algebraMap_residueField_injective :
    Function.Injective (algebraMap K v.ResidueField) :=
  (algebraMap K v.ResidueField).injective


theorem algebraMap_residueInv (hv : v.IsRational) (x : v.ResidueField) :
    algebraMap K v.ResidueField (v.residueInv x) = x :=
  Function.invFun_eq (hv x)

theorem residueInv_algebraMap (a : K) : v.residueInv (algebraMap K v.ResidueField a) = a :=
  Function.leftInverse_invFun v.algebraMap_residueField_injective a

open Classical in


theorem evalAt_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt f = v.residueInv (residue v.toValuationSubring ⟨f, hf⟩) :=
  dite_eq_left hf

theorem algebraMap_evalAt (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    algebraMap K v.ResidueField (v.evalAt f)
      = residue v.toValuationSubring (⟨f, hf⟩ : v.toValuationSubring) := by
  rw [v.evalAt_of_mem hf]
  exact v.algebraMap_residueInv hv _

@[simp]
theorem evalAt_one : v.evalAt (1 : F) = 1 := by
  rw [v.evalAt_of_mem (one_mem _)]
  have h1 : (⟨(1 : F), one_mem _⟩ : v.toValuationSubring) = 1 := rfl
  rw [h1, map_one, ← map_one (algebraMap K v.ResidueField), v.residueInv_algebraMap]

end Place

namespace Divisor


theorem evalFun_def (f : F) (D : Divisor K F) :
    evalFun f D = ∏ v ∈ D.support, v.evalAt f ^ D v := rfl

@[simp]
theorem evalFun_zero (f : F) : evalFun f (0 : Divisor K F) = 1 :=
  Finsupp.prod_zero_index

theorem evalFun_single (f : F) (v : Place K F) (n : ℤ) :
    evalFun f (Finsupp.single v n) = v.evalAt f ^ n :=
  Finsupp.prod_single_index (zpow_zero _)

end Divisor

variable (K F) in


end AlgebraicCurve
