import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Dirac


/--
[dirac](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Dirac.lean)
-/
@[path]
private lemma dirac_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
-- given
  (hcard : 3 ≤ Fintype.card V)
  (hdeg : ∀ v : V, Fintype.card V ≤ 2 * G.degree v) :
-- imply
  G.IsHamiltonian := by
-- proof
  apply dirac G hcard hdeg


-- created on 2026-10-20
