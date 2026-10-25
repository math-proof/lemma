import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairFractionalTransport.Part3
open Finset Matrix Polynomial StatMech StatMech.FrontierD


/--
[FiniteFractionalTransport.total_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairFractionalTransport.lean)
-/
@[path]
private lemma total_le_eq
  [Fintype Source]
  [Fintype Target]
  {sourceMass : Source -> Real}
  {targetCapacity : Target -> Real}
  {transport : FiniteFractionalTransport Source Target sourceMass targetCapacity} :
-- imply
  (∑ source, sourceMass source) <= ∑ target, targetCapacity target := by
-- proof
  apply StatMech.FrontierD.FiniteFractionalTransport.total_le transport

/--
[FiniteFractionalTransportOn.total_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairFractionalTransport.lean)
-/
@[path]
private lemma total_le_eq_2
  [Fintype Source]
  [Fintype Target]
  {sourceMass : Source -> Real}
  {targetCapacity : Target -> Real}
  {related : Source -> Target -> Prop}
  {transport : FiniteFractionalTransportOn Source Target sourceMass targetCapacity related} :
-- imply
  (∑ source, sourceMass source) <= ∑ target, targetCapacity target := by
-- proof
  apply StatMech.FrontierD.FiniteFractionalTransportOn.total_le transport

/--
[sixVertexMarkedSectorPairMass_le_of_fractionalTransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairFractionalTransport.lean)
-/
@[path]
private lemma sixVertexMarkedSectorPairMass_le_of_fractionalTransport_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {k : Nat}
  {transport : SixVertexMarkedPairFractionalTransport T lower middle upper k} :
-- imply
  sixVertexMarkedSectorPairMass T lower upper k <= sixVertexMarkedSectorPairMass T middle middle k := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedSectorPairMass_le_of_fractionalTransport transport

/--
[sixVertexMarkedSectorPairMass_le_of_fractionalTransportOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairFractionalTransport.lean)
-/
@[path]
private lemma sixVertexMarkedSectorPairMass_le_of_fractionalTransportOn_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {k : Nat}
  {related : SixVertexMarkedPairSource T lower upper -> SixVertexMarkedPairTarget T middle -> Prop}
  {transport : SixVertexMarkedPairFractionalTransportOn T lower middle upper k related} :
-- imply
  sixVertexMarkedSectorPairMass T lower upper k <= sixVertexMarkedSectorPairMass T middle middle k := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedSectorPairMass_le_of_fractionalTransportOn transport

/--
[coeff_shiftedSectorTrace_mul_le_sq_of_fractionalTransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairFractionalTransport.lean)
-/
@[path]
private lemma coeff_shiftedSectorTrace_mul_le_sq_of_fractionalTransport_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {k : Nat}
  {transport : SixVertexMarkedPairFractionalTransport T lower middle upper k} :
-- imply
  (sixVertexShiftedSectorTracePolynomial T.width T.height lower.val * sixVertexShiftedSectorTracePolynomial T.width T.height upper.val).coeff k <= (sixVertexShiftedSectorTracePolynomial T.width T.height middle.val ^ 2).coeff k := by
-- proof
  apply StatMech.FrontierD.coeff_shiftedSectorTrace_mul_le_sq_of_fractionalTransport transport

/--
[coeff_shiftedSectorTrace_mul_le_sq_of_fractionalTransportOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairFractionalTransport.lean)
-/
@[path]
private lemma coeff_shiftedSectorTrace_mul_le_sq_of_fractionalTransportOn_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {k : Nat}
  {related : SixVertexMarkedPairSource T lower upper -> SixVertexMarkedPairTarget T middle -> Prop}
  {transport : SixVertexMarkedPairFractionalTransportOn T lower middle upper k related} :
-- imply
  (sixVertexShiftedSectorTracePolynomial T.width T.height lower.val * sixVertexShiftedSectorTracePolynomial T.width T.height upper.val).coeff k <= (sixVertexShiftedSectorTracePolynomial T.width T.height middle.val ^ 2).coeff k := by
-- proof
  apply StatMech.FrontierD.coeff_shiftedSectorTrace_mul_le_sq_of_fractionalTransportOn transport


-- created on 2026-10-23
