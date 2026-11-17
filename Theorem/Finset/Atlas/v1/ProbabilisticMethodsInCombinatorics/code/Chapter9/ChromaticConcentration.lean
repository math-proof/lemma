module

public import Mathlib
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.ChromaticConcentration

public section

open MeasureTheory Measure SimpleGraph Real ChromaticConcentration


namespace ChromaticConcentration

/--
[DiffOnlyAt.symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/ChromaticConcentration.lean)
-/
public theorem DiffOnlyAt.symm
  {G G' : SimpleGraph V}
  {v : V}
-- given
  (h : DiffOnlyAt G G' v) :
-- imply
  DiffOnlyAt G' G v :=
-- proof
  fun a b ha hb => (h a b ha hb).symm

end ChromaticConcentration


-- created on 2026-10-23
