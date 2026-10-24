import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenTraceLogConcavity
open Filter Matrix Topology StatMech StatMech.FrontierD


/--
[sixVertexPositiveEvenHeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenTraceLogConcavity.lean)
-/
@[path]
private lemma sixVertexPositiveEvenHeight_pos_eq
  {M : Nat} :
-- imply
  0 < sixVertexPositiveEvenHeight M := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveEvenHeight_pos M

/--
[sixVertexPositiveEvenHeight_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenTraceLogConcavity.lean)
-/
@[path]
private lemma sixVertexPositiveEvenHeight_even_eq
  {M : Nat} :
-- imply
  Even (sixVertexPositiveEvenHeight M) := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveEvenHeight_even M

/--
[tendsto_sixVertexPositiveEvenHeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenTraceLogConcavity.lean)
-/
@[path]
private lemma tendsto_sixVertexPositiveEvenHeight_eq :
-- imply
  Tendsto sixVertexPositiveEvenHeight atTop atTop := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexPositiveEvenHeight

/--
[sixVertexSectorPerronLogConcave_of_positiveEvenTraceLogConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenTraceLogConcavity.lean)
-/
@[path]
private lemma sixVertexSectorPerronLogConcave_of_positiveEvenTraceLogConcave_eq
  {N : Nat}
  {c : Real}
-- given
  (hc : 0 < c)
  (htrace : SixVertexSectorPositiveEvenTraceLogConcave N c) :
-- imply
  SixVertexSectorPerronLogConcave N c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPerronLogConcave_of_positiveEvenTraceLogConcave N hc htrace

/--
[sixVertexSectorPositiveEvenTraceLogConcave_of_keyCapacityHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenTraceLogConcavity.lean)
-/
@[path]
private lemma sixVertexSectorPositiveEvenTraceLogConcave_of_keyCapacityHall_eq
  {N : Nat}
  {c : Real}
-- given
  (hNpos : 0 < N)
  (hNeven : Even N)
  (hc : 2 <= c)
  (hHall : SixVertexPositiveEvenTraceKeyCapacityHall N hNpos hNeven) :
-- imply
  SixVertexSectorPositiveEvenTraceLogConcave N c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPositiveEvenTraceLogConcave_of_keyCapacityHall N hNpos hNeven hc hHall

/--
[sixVertexSectorPerronLogConcave_of_positiveEvenTraceKeyCapacityHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenTraceLogConcavity.lean)
-/
@[path]
private lemma sixVertexSectorPerronLogConcave_of_positiveEvenTraceKeyCapacityHall_eq
  {N : Nat}
  {c : Real}
-- given
  (hNpos : 0 < N)
  (hNeven : Even N)
  (hc : 2 <= c)
  (hHall : SixVertexPositiveEvenTraceKeyCapacityHall N hNpos hNeven) :
-- imply
  SixVertexSectorPerronLogConcave N c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPerronLogConcave_of_positiveEvenTraceKeyCapacityHall N hNpos hNeven hc hHall


-- created on 2026-10-23
