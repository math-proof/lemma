import Mathlib
import sympy.Basic
import Def.Combinatorics.SimpleGraph.Ramsey
open SimpleGraph


namespace SimpleGraph

/--
[graphRamsey_eq_sInf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Ramsey.lean)
-/
@[path]
lemma graphRamsey_eq_sInf
  {s t : ℕ} :
-- imply
  graphRamsey s t = sInf {N : ℕ | classicalRamsey s t N} :=
-- proof
  rfl

end SimpleGraph

namespace SimpleGraph

/--
[graphPairRamsey_eq_sInf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Ramsey.lean)
-/
@[path]
lemma graphPairRamsey_eq_sInf
  [Fintype α] [Fintype β]
  {G : SimpleGraph α}
  {H : SimpleGraph β} :
-- imply
  graphPairRamsey G H =
      sInf {n : ℕ | ∀ C : SimpleGraph (Fin n), G.IsContained C ∨ H.IsContained Cᶜ} :=
-- proof
  rfl

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-23
