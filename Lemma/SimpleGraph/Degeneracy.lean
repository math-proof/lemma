import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Degeneracy
open SimpleGraph


namespace SimpleGraph

/--
[IsDegenerateOn.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Degeneracy.lean)
-/
@[path]
lemma IsDegenerateOn.mono
  [Finite V]
  {G : SimpleGraph V}
  {U T : Set V}
  {k l : ℕ}
-- given
  (h : G.IsDegenerateOn U k)
  (hkl : k ≤ l) :
-- imply
  G.IsDegenerateOn U l := by
-- proof
  intro W hWne hWU
  obtain ⟨v, hvW, hv⟩ := h W hWne hWU
  exact ⟨v, hvW, hv.trans hkl⟩

end SimpleGraph

namespace SimpleGraph

/--
[IsDegenerateOn.of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Degeneracy.lean)
-/
@[path]
lemma IsDegenerateOn.of_subset
  [Finite V]
  {G : SimpleGraph V}
  {U T : Set V}
  {k l : ℕ}
-- given
  (h : G.IsDegenerateOn U k)
  (hTU : T ⊆ U) :
-- imply
  G.IsDegenerateOn T k := by
-- proof
  intro W hWne hWT
  exact h W hWne (hWT.trans hTU)

end SimpleGraph

namespace SimpleGraph

/--
[IsDegenerate.isDegenerateOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Degeneracy.lean)
-/
@[path]
lemma IsDegenerate.isDegenerateOn
  [Finite V]
  {G : SimpleGraph V}
  {U T : Set V}
  {k l : ℕ}
  {U : Set V}
-- given
  (h : G.IsDegenerate k) :
-- imply
  G.IsDegenerateOn U k :=
-- proof
  h.of_subset (Set.subset_univ U)

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-23
