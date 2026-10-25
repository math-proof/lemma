import Mathlib
import Instance.AutomorphicForm_Gamma0FundamentalSet
import Abbrev.AutomorphicForm_L2AutomorphicCarrier
import Lemma.AutomorphicForm.TruncatedDomainPartition

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup CongruenceSubgroup
open MeasureTheory
open scoped Modular MatrixGroups Pointwise ENNReal

noncomputable section

namespace FLT.L2ProductionInstance

open FLT.Gamma0FundamentalSet FLT.L2Carrier


abbrev Gamma0L2 (N : ℕ) : Type :=
  AutomorphicL2 (gammaFundamentalSet (Gamma0 N))


end FLT.L2ProductionInstance

end
