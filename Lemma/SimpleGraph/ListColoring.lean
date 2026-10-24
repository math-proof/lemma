import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.ListColoring
open SimpleGraph


namespace SimpleGraph

/--
[IsListColorable.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ListColoring.lean)
-/
@[path]
lemma IsListColorable.mono
  {G : SimpleGraph V}
  {q r : ℕ}
-- given
  (hG : G.IsListColorable q)
  (hqr : q ≤ r) :
-- imply
  G.IsListColorable r := by
-- proof
  intro C _ lists hlists
  exact hG C lists fun v => hqr.trans (hlists v)

end SimpleGraph

namespace SimpleGraph

/--
[IsListColorable.colorable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ListColoring.lean)
-/
@[path]
lemma IsListColorable.colorable
  {G : SimpleGraph V}
  {q r : ℕ}
-- given
  (hG : G.IsListColorable q) :
-- imply
  G.Colorable q := by
-- proof
  let lists : V → Finset (Fin q) := fun _ => Finset.univ
  obtain ⟨color, _⟩ := hG (Fin q) lists (by simp [lists])
  exact ⟨color⟩

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-23
