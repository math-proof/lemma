import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Frucht
open MathlibExt.Combinatorics.SimpleGraph.FruchtWanted


/--
[frucht](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Frucht.lean)
-/
@[path]
private lemma frucht_eq
  [Group G] [Fintype G] [DecidableEq G] :
-- imply
  ∃ (n : ℕ) (Γ : SimpleGraph (Fin n)), Nonempty (G ≃* (Γ ≃g Γ)) := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.FruchtWanted.frucht


-- created on 2026-10-20
