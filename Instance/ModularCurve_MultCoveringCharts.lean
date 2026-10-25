-- Carved from Lemma/Definitions/Def_ModularCurve_MultCoveringCharts.lean: instance decls only.
import Lemma.AlgebraicCurve.SemistableCharts
import Def.AlgebraicCurve_ChordalProximity
import Lemma.ModularCurve.SupersingularModuli
import Structure.ModularCurve_LevelOneProlongationPair
import Lemma.AlgebraicCurve.SemistableChartsComap
import Lemma.ModularCurve.LevelOneChartFst

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
