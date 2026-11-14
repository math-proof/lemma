-- Carved from Lemma/Definitions/Def_ModularCurve_MultCoveringCharts.lean: instance decls only.
import Lemma.ValuationSubring.SemistableCharts
import Def.AlgebraicCurve_ChordalProximity
import Lemma.WeierstrassCurve.SupersingularModuli
import Structure.ModularCurve_LevelOneProlongationPair
import Lemma.AlgEquiv.SemistableChartsComap
import Lemma.ResidueField.LevelOneChartFst

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option autoImplicit false

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve.MultCovering

section Instances
variable (A : ValuationSubring (AlgebraicClosure ℚ))

instance instFieldFbar : Field ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) := inferInstance

instance instAlgebraFbar :
    Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
  inferInstance

end Instances


end ModularCurve.MultCovering

end
