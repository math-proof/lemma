import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc3_orbitkeysymm
open Finset StatMech StatMech.Walls


/--
[rc3_orbitKey_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_orbitkeysymm.lean)
-/
@[path]
private lemma rc3_orbitKey_symm_eq
  {a b : ConfigSpace α} :
-- imply
  orbitKey (a, b) = orbitKey (b, a) := by
-- proof
  apply StatMech.Walls.rc3_orbitKey_symm a b

/--
[rc3_orbitKey_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc3_orbitkeysymm.lean)
-/
@[path]
private lemma rc3_orbitKey_swap_eq
  {p : ConfigSpace α × ConfigSpace α} :
-- imply
  orbitKey (p.2, p.1) = orbitKey p := by
-- proof
  apply StatMech.Walls.rc3_orbitKey_swap p


-- created on 2026-10-23
