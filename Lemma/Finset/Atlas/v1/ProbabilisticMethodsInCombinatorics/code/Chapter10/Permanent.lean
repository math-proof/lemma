import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Permanent
open Finset Matrix BigOperators KahnLovasz
open SimpleGraph Finset BigOperators


namespace KahnLovasz

/--
[adjMatrix_rowSumGen_eq_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Permanent.lean)
-/
@[path]
lemma adjMatrix_rowSumGen_eq_degree
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v : V} :
-- imply
  BregmanMinc.rowSumGen (G.adjMatrix ℝ) v = G.degree v := by
-- proof
  unfold BregmanMinc.rowSumGen SimpleGraph.degree
  congr 1
  ext w
  simp only [SimpleGraph.adjMatrix_apply, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.mem_neighborFinset]
  constructor
  · intro h
    split_ifs at h with hadj
    · exact hadj
    · norm_num at h
  · intro hadj
    simp [hadj]
/-- The Kahn-Lovász inequality (Corollary 10.2.2): the number of perfect matchings of $G$
satisfies $|\mathcal{M}(G)| \le \prod_v (\deg(v)!)^{1/(2\deg(v))}$. -/

end KahnLovasz


-- created on 2026-10-23
