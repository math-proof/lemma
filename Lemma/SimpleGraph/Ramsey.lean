import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Ramsey
open SimpleGraph


/--
[graphRamsey_eq_sInf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Ramsey.lean)
-/
@[path]
private lemma graphRamsey_eq_sInf_eq
  {s t : ℕ} :
-- imply
  graphRamsey s t = sInf {N : ℕ | classicalRamsey s t N} := by
-- proof
  apply SimpleGraph.graphRamsey_eq_sInf s t

/--
[graphPairRamsey_eq_sInf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Ramsey.lean)
-/
@[path]
private lemma graphPairRamsey_eq_sInf_eq
  [Fintype α] [Fintype β]
  {G : SimpleGraph α}
  {H : SimpleGraph β} :
-- imply
  graphPairRamsey G H =
      sInf {n : ℕ | ∀ C : SimpleGraph (Fin n), G.IsContained C ∨ H.IsContained Cᶜ} := by
-- proof
  apply SimpleGraph.graphPairRamsey_eq_sInf G H


-- created on 2026-10-20
