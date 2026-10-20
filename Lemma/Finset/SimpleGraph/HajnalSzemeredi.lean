import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.HajnalSzemeredi
open MathlibExt.Combinatorics.SimpleGraph.HajnalSzemerediWanted


/--
[exists_equitable_coloring_of_maxDegree_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HajnalSzemeredi.lean)
-/
@[path]
private lemma exists_equitable_coloring_of_maxDegree_lt_eq
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ}
-- given
  (hk : G.maxDegree < k) :
-- imply
  ∃ C : G.Coloring (Fin k),
    ∀ i j : Fin k, (C.colorClass i).ncard ≤ (C.colorClass j).ncard + 1 := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.HajnalSzemerediWanted.exists_equitable_coloring_of_maxDegree_lt G k hk

/--
[hajnal_szemeredi_equitable_coloring](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HajnalSzemeredi.lean)
-/
@[path]
private lemma hajnal_szemeredi_equitable_coloring_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {k : ℕ}
-- given
  (hk : G.maxDegree < k) :
-- imply
  ∃ C : G.Coloring (Fin k),
    ∀ i j : Fin k, (C.colorClass i).ncard ≤ (C.colorClass j).ncard + 1 := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.HajnalSzemerediWanted.hajnal_szemeredi_equitable_coloring G k hk


-- created on 2026-10-20
