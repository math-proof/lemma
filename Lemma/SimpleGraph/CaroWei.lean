import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.CaroWei
open SimpleGraph


/--
[exists_isIndepSet_caroWei](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/CaroWei.lean)
-/
@[path]
private lemma exists_isIndepSet_caroWei_eq
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj] :
-- imply
  ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧
    ∑ v, (1 : ℝ) / (G.degree v + 1) ≤ s.card := by
-- proof
  apply SimpleGraph.exists_isIndepSet_caroWei

/--
[caroWei_le_indepNum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/CaroWei.lean)
-/
@[path]
private lemma caroWei_le_indepNum_eq
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj] :
-- imply
  ∑ v, (1 : ℝ) / (G.degree v + 1) ≤ G.indepNum := by
-- proof
  apply SimpleGraph.caroWei_le_indepNum


-- created on 2026-10-20
