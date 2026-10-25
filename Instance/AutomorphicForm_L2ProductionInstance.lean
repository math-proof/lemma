-- Carved from Lemma/Definitions/Def_AutomorphicForm_L2ProductionInstance.lean: instance decls only.
import Mathlib

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup CongruenceSubgroup
open MeasureTheory
open scoped Modular MatrixGroups Pointwise ENNReal

noncomputable section

namespace FLT.L2ProductionInstance

open FLT.Gamma0FundamentalSet FLT.L2Carrier


instance countable_SL2Z : Countable SL(2, ℤ) :=
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  inferInstanceAs (Countable { A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1 })

instance countable_quotient (Γ : Subgroup SL(2, ℤ)) : Countable (SL(2, ℤ) ⧸ Γ) :=
  Quotient.countable


instance isFiniteMeasure_gamma0 (N : ℕ) [NeZero N] :
    IsFiniteMeasure ((volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))) :=
  isFiniteMeasure_restrict_of_lt_top (volume_gamma0_lt_top N)

example (N : ℕ) : NormedAddCommGroup (Gamma0L2 N) := inferInstance

example (N : ℕ) : InnerProductSpace ℂ (Gamma0L2 N) := inferInstance

example (N : ℕ) : CompleteSpace (Gamma0L2 N) := inferInstance


instance nontrivial_gamma0L2 (N : ℕ) [NeZero N] : Nontrivial (Gamma0L2 N) :=
  ⟨gamma0L2Const N, 0, gamma0L2Const_ne_zero N⟩


end FLT.L2ProductionInstance

end
