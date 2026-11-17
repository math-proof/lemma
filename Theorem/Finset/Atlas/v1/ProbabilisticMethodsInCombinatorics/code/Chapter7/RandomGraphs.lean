module

public import Mathlib
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter7.RandomGraphs

public section

open Finset BigOperators RandomGraphs


namespace RandomGraphs

/--
[notTriangleEvent_isDecreasing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter7/RandomGraphs.lean)
-/
public theorem notTriangleEvent_isDecreasing
  {n : ℕ}
  {t : Triple n} :
-- imply
  IsDecreasing (notTriangleEvent t) := by
-- proof
  intro G H hG hHG
  simp only [notTriangleEvent, Set.mem_setOf_eq] at *
  intro ⟨h1, h2, h3⟩
  exact hG ⟨hHG _ h1, hHG _ h2, hHG _ h3⟩

end RandomGraphs


-- created on 2026-10-23
