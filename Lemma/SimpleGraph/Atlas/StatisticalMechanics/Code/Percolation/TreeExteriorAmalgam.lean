import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.TreeExteriorAmalgam
open Set SimpleGraph StatMech StatMech.Percolation


/--
[tree_exterior_amalgam_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreeExteriorAmalgam.lean)
-/
@[path]
private lemma tree_exterior_amalgam_separated_eq
  {T : SimpleGraph W}
  {E U : SimpleGraph V}
  {embed : W → V}
  {leaf : Fin 3 → W}
-- given
  (hembed : Function.Injective embed)
  (hub : W)
  (hcut : ∀ i j, i ≠ j → ¬ (T.deleteIncidenceSet hub).Reachable (leaf i) (leaf j))
  (hEsep : ∀ i j, i ≠ j → ¬ E.Reachable (embed (leaf i)) (embed (leaf j)))
  (hEonly : ∀ z y, E.Adj (embed z) y → ∃ i, z = leaf i)
  (hUdecomp : ∀ {x y}, U.Adj x y → E.Adj x y ∨ ∃ a b, T.Adj a b ∧ embed a = x ∧ embed b = y) :
-- imply
  ∀ i j, i ≠ j → ¬ (U.deleteIncidenceSet (embed hub)).Reachable (embed (leaf i)) (embed (leaf j)) := by
-- proof
  apply StatMech.Percolation.tree_exterior_amalgam_separated T E U embed hembed hub leaf hcut hEsep hEonly hUdecomp


-- created on 2026-10-23
