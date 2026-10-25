-- Carved from Lemma/Definitions/Def_AutomorphicForm_Gamma0FundamentalSet.lean: instance decls only.
import Mathlib
import Lemma.AutomorphicForm.FundamentalDomainVolume
import Lemma.UpperHalfPlane.SiegelSetCover

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup CongruenceSubgroup
open MeasureTheory
open scoped Modular MatrixGroups Pointwise

namespace FLT.Gamma0FundamentalSet

instance : ContinuousConstSMul SL(2, ℤ) ℍ where
  continuous_const_smul γ := by
    have h : (fun z : ℍ => γ • z) =
        fun z : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ γ) • z := by
      funext z
      exact MulAction.compHom_smul_def (Matrix.SpecialLinearGroup.mapGL ℝ) γ z
    rw [h]
    exact continuous_const_smul _

end FLT.Gamma0FundamentalSet
