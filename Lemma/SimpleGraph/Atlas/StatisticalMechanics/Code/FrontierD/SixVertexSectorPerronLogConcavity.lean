import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
open Finset Matrix Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexSectorPerronProfile_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorPerronLogConcavity.lean)
-/
@[path]
private lemma sixVertexSectorPerronProfile_eq_eq
  {N n : Nat}
  {c : Real}
-- given
  (hn : n <= N) :
-- imply
  sixVertexSectorPerronProfile N c n = sixVertexSectorTopEigenvalue N n hn c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPerronProfile_eq hn c

/--
[sixVertexSectorPerronProfile_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorPerronLogConcavity.lean)
-/
@[path]
private lemma sixVertexSectorPerronProfile_pos_eq
  {N n : Nat}
  {c : Real}
-- given
  (hn : n <= N)
  (hc : 0 < c) :
-- imply
  0 < sixVertexSectorPerronProfile N c n := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPerronProfile_pos hn hc

/--
[sixVertexSectorPerronProfile_particleHole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorPerronLogConcavity.lean)
-/
@[path]
private lemma sixVertexSectorPerronProfile_particleHole_eq
  {N n : Nat}
  {c : Real}
-- given
  (hn : n <= N) :
-- imply
  sixVertexSectorPerronProfile N c (N - n) = sixVertexSectorPerronProfile N c n := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPerronProfile_particleHole hn c

/--
[sixVertexSectorTraceProfile_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorPerronLogConcavity.lean)
-/
@[path]
private lemma sixVertexSectorTraceProfile_eq_eq
  {N M n : Nat}
  {c : Real}
-- given
  (hn : n <= N) :
-- imply
  sixVertexSectorTraceProfile N M c n = Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTraceProfile_eq hn c

/--
[sixVertexSectorPerronLogConcave_of_traceLogConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorPerronLogConcavity.lean)
-/
@[path]
private lemma sixVertexSectorPerronLogConcave_of_traceLogConcave_eq
  {N : Nat}
  {c : Real}
-- given
  (hc : 0 < c)
  (htrace : SixVertexSectorTraceLogConcave N c) :
-- imply
  SixVertexSectorPerronLogConcave N c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPerronLogConcave_of_traceLogConcave N hc htrace

/--
[adjacentRatio_antitone_of_pos_logConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorPerronLogConcavity.lean)
-/
@[path]
private lemma adjacentRatio_antitone_of_pos_logConcave_eq
  {N : Nat}
  {i j : Nat}
-- given
  (a : Nat -> Real)
  (hpos : forall n, n <= N -> 0 < a n)
  (hlc : forall n, 0 < n -> n < N -> a (n - 1) * a (n + 1) <= a n ^ 2)
  (hij : i <= j)
  (hj : j < N) :
-- imply
  a (j + 1) / a j <= a (i + 1) / a i := by
-- proof
  apply StatMech.FrontierD.adjacentRatio_antitone_of_pos_logConcave a N hpos hlc hij hj

/--
[adjacent_le_of_pos_logConcave_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorPerronLogConcavity.lean)
-/
@[path]
private lemma adjacent_le_of_pos_logConcave_symmetric_eq
  {N : Nat}
  {i : Nat}
-- given
  (a : Nat -> Real)
  (hN : Even N)
  (hpos : forall n, n <= N -> 0 < a n)
  (hsym : forall n, n <= N -> a (N - n) = a n)
  (hlc : forall n, 0 < n -> n < N -> a (n - 1) * a (n + 1) <= a n ^ 2)
  (hi : i < N / 2) :
-- imply
  a i <= a (i + 1) := by
-- proof
  apply StatMech.FrontierD.adjacent_le_of_pos_logConcave_symmetric a N hN hpos hsym hlc hi

/--
[lowerHalf_le_middle_of_pos_logConcave_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorPerronLogConcavity.lean)
-/
@[path]
private lemma lowerHalf_le_middle_of_pos_logConcave_symmetric_eq
  {N : Nat}
  {i : Nat}
-- given
  (a : Nat -> Real)
  (hN : Even N)
  (hpos : forall n, n <= N -> 0 < a n)
  (hsym : forall n, n <= N -> a (N - n) = a n)
  (hlc : forall n, 0 < n -> n < N -> a (n - 1) * a (n + 1) <= a n ^ 2)
  (hi : i <= N / 2) :
-- imply
  a i <= a (N / 2) := by
-- proof
  apply StatMech.FrontierD.lowerHalf_le_middle_of_pos_logConcave_symmetric a N hN hpos hsym hlc hi

/--
[sixVertexSectorPerronProfile_lowerHalf_le_middle_of_logConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorPerronLogConcavity.lean)
-/
@[path]
private lemma sixVertexSectorPerronProfile_lowerHalf_le_middle_of_logConcave_eq
  {N : Nat}
  {c : Real}
  {n : Nat}
-- given
  (hN : Even N)
  (hc : 0 < c)
  (hlc : SixVertexSectorPerronLogConcave N c)
  (hn : n <= N / 2) :
-- imply
  sixVertexSectorTopEigenvalue N n (hn.trans (Nat.div_le_self N 2)) c <= sixVertexSectorTopEigenvalue N (N / 2) (Nat.div_le_self N 2) c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPerronProfile_lowerHalf_le_middle_of_logConcave N hN hc hlc n hn

/--
[sixVertexWidthTopEigenvalue_eq_halfFilled_of_logConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorPerronLogConcavity.lean)
-/
@[path]
private lemma sixVertexWidthTopEigenvalue_eq_halfFilled_of_logConcave_eq
  {N : Nat}
  {c : Real}
-- given
  (hN : Even N)
  (hc : 0 < c)
  (hlc : SixVertexSectorPerronLogConcave N c) :
-- imply
  sixVertexWidthTopEigenvalue N c = sixVertexSectorTopEigenvalue N (N / 2) (Nat.div_le_self N 2) c := by
-- proof
  apply StatMech.FrontierD.sixVertexWidthTopEigenvalue_eq_halfFilled_of_logConcave N hN hc hlc


-- created on 2026-10-23
