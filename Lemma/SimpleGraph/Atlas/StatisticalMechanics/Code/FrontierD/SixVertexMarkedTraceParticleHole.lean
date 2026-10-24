import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceParticleHole
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexShiftedSectorTransferPolynomial_particleHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceParticleHole.lean)
-/
@[path]
private lemma sixVertexShiftedSectorTransferPolynomial_particleHole_eq
  {N n : Nat}
  {x y : SixVertexSector N n}
-- given
  (hn : n <= N) :
-- imply
  sixVertexShiftedSectorTransferPolynomial N (N - n) (sixVertexSectorParticleHoleEquiv N n hn x) (sixVertexSectorParticleHoleEquiv N n hn y) = sixVertexShiftedSectorTransferPolynomial N n x y := by
-- proof
  apply StatMech.FrontierD.sixVertexShiftedSectorTransferPolynomial_particleHole hn x y

/--
[matrix_trace_pow_eq_of_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceParticleHole.lean)
-/
@[path]
private lemma matrix_trace_pow_eq_of_equiv_eq
  [Fintype alpha]
  [Fintype beta]
  [DecidableEq alpha]
  [DecidableEq beta]
  [CommSemiring R]
  {e : alpha ≃ beta}
  {A : Matrix alpha alpha R}
  {B : Matrix beta beta R}
  {M : Nat}
-- given
  (hentry : forall x y, B (e x) (e y) = A x y) :
-- imply
  Matrix.trace (B ^ M) = Matrix.trace (A ^ M) := by
-- proof
  apply StatMech.FrontierD.matrix_trace_pow_eq_of_equiv e A B hentry M

/--
[sixVertexShiftedSectorTracePolynomial_particleHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceParticleHole.lean)
-/
@[path]
private lemma sixVertexShiftedSectorTracePolynomial_particleHole_eq
  {N n : Nat}
  {M : Nat}
-- given
  (hn : n <= N) :
-- imply
  sixVertexShiftedSectorTracePolynomial N M (N - n) = sixVertexShiftedSectorTracePolynomial N M n := by
-- proof
  apply StatMech.FrontierD.sixVertexShiftedSectorTracePolynomial_particleHole hn M

/--
[sixVertexMarkedSectorTraceCoefficient_particleHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceParticleHole.lean)
-/
@[path]
private lemma sixVertexMarkedSectorTraceCoefficient_particleHole_eq
  {N n : Nat}
  {M k : Nat}
-- given
  (hn : n <= N) :
-- imply
  sixVertexMarkedSectorTraceCoefficient N M (N - n) k = sixVertexMarkedSectorTraceCoefficient N M n k := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedSectorTraceCoefficient_particleHole hn M k

/--
[sixVertexMarkedTraceLogConcavityDifference_particleHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceParticleHole.lean)
-/
@[path]
private lemma sixVertexMarkedTraceLogConcavityDifference_particleHole_eq
  {N n : Nat}
  {M : Nat}
-- given
  (hn0 : 0 < n)
  (hnN : n < N) :
-- imply
  sixVertexMarkedTraceLogConcavityDifference N M (N - n) = sixVertexMarkedTraceLogConcavityDifference N M n := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceLogConcavityDifference_particleHole hn0 hnN M

/--
[markedCoefficientwiseLogConcave_of_lowerHalf_suffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceParticleHole.lean)
-/
@[path]
private lemma markedCoefficientwiseLogConcave_of_lowerHalf_suffix_eq
  {N M : Nat}
-- given
  (hsuffix : forall n : Nat, 0 < n -> n <= N / 2 -> SixVertexMarkedAntidiagonalSuffixNonnegative N M n) :
-- imply
  forall n : Nat, 0 < n -> n < N -> SixVertexMarkedTraceCoefficientwiseLogConcave N M n := by
-- proof
  apply StatMech.FrontierD.markedCoefficientwiseLogConcave_of_lowerHalf_suffix N M hsuffix


-- created on 2026-10-23
