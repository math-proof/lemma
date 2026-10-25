import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.HypergraphColoring2
open Set Topology HypergraphColoring


namespace HypergraphColoring

/--
[isClosed_not_all_eq624](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/HypergraphColoring2.lean)
-/
@[path]
lemma isClosed_not_all_eq624
  {e : Finset V}
  {b : Bool} :
-- imply
  IsClosed {c : V → Bool | ¬(∀ v ∈ e, c v = b)} := by
-- proof
  have heq : {c : V → Bool | ¬(∀ v ∈ e, c v = b)} = (Set.pi (↑e) (fun _ => {b}))ᶜ := by
    ext c; simp [Set.mem_pi]
  rw [heq]
  exact (isOpen_set_pi e.finite_toSet (fun _ _ => @isOpen_discrete Bool _ _ {b})).isClosed_compl

end HypergraphColoring

namespace HypergraphColoring

/--
[isClosed_goodColorings624](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/HypergraphColoring2.lean)
-/
@[path]
lemma isClosed_goodColorings624
  {edges : Set (Finset V)}
  {X : Finset V} :
-- imply
  IsClosed (goodColorings624 edges X) := by
-- proof
  have heq : goodColorings624 edges X =
    ⋂ (e : Finset V) (_ : e ∈ edges) (_ : (↑e : Set V) ⊆ ↑X),
      ({c : V → Bool | ¬(∀ v ∈ e, c v = true)} ∩
        {c | ¬(∀ v ∈ e, c v = false)}) := by
    ext c; simp only [goodColorings624, mem_setOf_eq, mem_iInter, mem_inter_iff]
  rw [heq]
  apply isClosed_iInter; intro e
  apply isClosed_iInter; intro _
  apply isClosed_iInter; intro _
  exact IsClosed.inter (isClosed_not_all_eq624 e true) (isClosed_not_all_eq624 e false)

end HypergraphColoring

namespace HypergraphColoring

/--
[goodColorings624_anti](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/HypergraphColoring2.lean)
-/
@[path]
lemma goodColorings624_anti
  {edges : Set (Finset V)}
  {X Y : Finset V}
-- given
  (hYX : Y ⊆ X) :
-- imply
  goodColorings624 edges X ⊆ goodColorings624 edges Y := by
-- proof
  intro c hc e he hes
  exact hc e he (hes.trans (Finset.coe_subset.mpr hYX))
/-- Empty.Finite-vertex version of Corollary 6.1.10 applied to hypergraph 2-coloring: if every edge
has size $\ge 3$ and the LLL weight bound $\sum_{f \in S} 2^{-|f|} \le 1/8$ holds for every
finite collection of intersecting neighboring edges, then there is a proper 2-coloring of every
finite vertex set `X`. -/

end HypergraphColoring


-- created on 2026-10-23
