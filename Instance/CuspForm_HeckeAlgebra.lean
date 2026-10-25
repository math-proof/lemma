-- Carved from Lemma/Definitions/Def_CuspForm_HeckeAlgebra.lean: instance decls only.
import Lemma.ModularForm.HeckeOperatorForms
import Theorems.Thm_CuspForm_heckeTLin_comm
import Theorems.Thm_CuspForm_heckeTLin_heckeULin_comm
import Theorems.Thm_CuspForm_heckeULin_comm
import Lemma.CuspForm.HeckeAlgebra

set_option autoImplicit false

noncomputable section

namespace CuspForm

variable (N : ℕ) [NeZero N] (k : ℤ) (S : Set ℕ)

variable {N k S}

variable (N k S)

instance heckeAlgebra.instIsMulCommutative : IsMulCommutative (heckeAlgebra N k S) :=
  Algebra.isMulCommutative_adjoin ℤ fun _ hT _ hT' => commute_of_mem_heckeGenerators hT hT'

open scoped IsMulCommutative in

instance heckeAlgebra.instCommRing : CommRing (heckeAlgebra N k S) := inferInstance

instance heckeAlgebra.instIsAddTorsionFree : IsAddTorsionFree (heckeAlgebra N k S) where
  nsmul_right_injective n hn a b hab := by
    apply Subtype.ext
    have h : (n : ℂ) • (a : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) =
        (n : ℂ) • (b : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) := by
      simp only [Nat.cast_smul_eq_nsmul]
      exact congrArg Subtype.val hab
    exact smul_right_injective _ (Nat.cast_ne_zero.mpr hn) h

variable {N k S}

end CuspForm

end
