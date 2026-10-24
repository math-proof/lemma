import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.SidorenkoConlonFoxSudakov
open Sidorenko


namespace Sidorenko

/--
[hasUniversalVertex_edgeFinset_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/SidorenkoConlonFoxSudakov.lean)
-/
@[path]
lemma hasUniversalVertex_edgeFinset_pos
  [Fintype A]
  [Fintype B]
  [DecidableEq A]
  [DecidableEq B]
  [Nonempty A]
  [Nonempty B]
  {F : SimpleGraph (A ⊕ B)}
  [DecidableRel F.Adj]
-- given
  (hF : HasUniversalVertex F) :
-- imply
  0 < F.edgeFinset.card := by
-- proof
  obtain ⟨a, ha⟩ | ⟨b, hb⟩ := hF
  · obtain ⟨b⟩ := ‹Nonempty B›
    have hadj := ha b
    have hmem : s(Sum.inl a, Sum.inr b) ∈ F.edgeFinset := by
      rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  · obtain ⟨a⟩ := ‹Nonempty A›
    have hadj := hb a
    have hmem : s(Sum.inr b, Sum.inl a) ∈ F.edgeFinset := by
      rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact Finset.card_pos.mpr ⟨_, hmem⟩
/-- Theorem 10.3.7 (Conlon-Fox-Sudakov 2010). Sidorenko's conjecture holds for any
bipartite graph $F$ that has a universal vertex on one side:
$\mathrm{hom\text{-}density}(F, G) \ge \mathrm{hom\text{-}density}(K_2, G)^{|E(F)|}$. -/

end Sidorenko


-- created on 2026-10-23
