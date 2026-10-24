import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface
open Finset Matrix Polynomial StatMech StatMech.FrontierD


/--
[sixVertexMarkedSectorConfigurationPolynomial_eq_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairSwitchInterface.lean)
-/
@[path]
private lemma sixVertexMarkedSectorConfigurationPolynomial_eq_trace_eq
  {T : EvenTorus}
  {n : Fin (T.width + 1)} :
-- imply
  sixVertexMarkedSectorConfigurationPolynomial T n = sixVertexShiftedSectorTracePolynomial T.width T.height n.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedSectorConfigurationPolynomial_eq_trace T n

/--
[sixVertexMarkedSectorPairMass_eq_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairSwitchInterface.lean)
-/
@[path]
private lemma sixVertexMarkedSectorPairMass_eq_coeff_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {k : Nat} :
-- imply
  sixVertexMarkedSectorPairMass T left right k = (sixVertexShiftedSectorTracePolynomial T.width T.height left.val * sixVertexShiftedSectorTracePolynomial T.width T.height right.val).coeff k := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedSectorPairMass_eq_coeff T left right k

/--
[sixVertexMarkedPairMultiplicity_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairSwitchInterface.lean)
-/
@[path]
private lemma sixVertexMarkedPairMultiplicity_nonneg_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {k : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule) :
-- imply
  0 <= sixVertexMarkedPairMultiplicity omega eta k := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedPairMultiplicity_nonneg omega eta homega heta k

/--
[sixVertexMarkedSectorPairMass_le_of_switch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairSwitchInterface.lean)
-/
@[path]
private lemma sixVertexMarkedSectorPairMass_le_of_switch_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {k : Nat}
  {S : SixVertexGlobalMarkedPairSwitch T lower middle upper k} :
-- imply
  sixVertexMarkedSectorPairMass T lower upper k <= sixVertexMarkedSectorPairMass T middle middle k := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedSectorPairMass_le_of_switch S

/--
[coeff_shiftedSectorTrace_mul_le_sq_of_globalMarkedPairSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairSwitchInterface.lean)
-/
@[path]
private lemma coeff_shiftedSectorTrace_mul_le_sq_of_globalMarkedPairSwitch_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {k : Nat}
  {S : SixVertexGlobalMarkedPairSwitch T lower middle upper k} :
-- imply
  (sixVertexShiftedSectorTracePolynomial T.width T.height lower.val * sixVertexShiftedSectorTracePolynomial T.width T.height upper.val).coeff k <= (sixVertexShiftedSectorTracePolynomial T.width T.height middle.val ^ 2).coeff k := by
-- proof
  apply StatMech.FrontierD.coeff_shiftedSectorTrace_mul_le_sq_of_globalMarkedPairSwitch S


-- created on 2026-10-23
