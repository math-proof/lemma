module
public import Theorem.ValuationSubring.SemistableCharts
public import Def.AlgebraicCurve_ChordalProximity
public import Theorem.WeierstrassCurve.SupersingularModuli
public import Structure.ModularCurve_LevelOneProlongationPair
public import Theorem.AlgEquiv.SemistableChartsComap
public import Theorem.ResidueField.LevelOneChartFst
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000


public section

-- Carved from Lemma/Definitions/Def_ModularCurve_MultCoveringCharts.lean: instance decls only.

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
