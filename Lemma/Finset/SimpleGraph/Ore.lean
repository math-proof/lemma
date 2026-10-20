import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Ore
open MathlibExt.Combinatorics.SimpleGraph.OreWanted


/--
[ore](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Ore.lean)
-/
@[path]
private lemma ore_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
-- given
  (hcard : 3 ≤ Fintype.card V)
  (hdeg : ∀ u v : V, u ≠ v → ¬G.Adj u v → Fintype.card V ≤ G.degree u + G.degree v) :
-- imply
  G.IsHamiltonian := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.OreWanted.ore G hcard hdeg


-- created on 2026-10-20
