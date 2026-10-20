/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/OrdinaryEhrhartCount.lean -/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Card

/-!
# Ordinary Ehrhart counts

This file records the ordinary lattice-point count used by Ryuichi Sakamoto,
*The h*-Polynomial of the Cut Polytope of K_{2,m} in the Lattice Spanned by
its Vertices*, Journal of Integer Sequences 23 (2020), Article 20.7.5.
-/

namespace MetaMathlibExt

/-- The ordinary Ehrhart count `|mP ∩ ℤ^d|`.

This is total on arbitrary sets: as usual, `Set.ncard` returns zero for an
infinite intersection. For polytopes the intersection is finite. Stable source
identifiers: concept `jis_sem_91fece955b8d30a79b80296c`, statement
`jis_52595824a0e5a66cf10405d1`.
-/
noncomputable def ordinaryEhrhartCount (d : ℕ) (P : Set (Fin d → ℚ)) (m : ℕ) : ℕ :=
  Set.ncard
    (((fun x : Fin d → ℚ => (m : ℚ) • x) '' P) ∩
      Set.range fun z : Fin d → ℤ => fun i => (z i : ℚ))

end MetaMathlibExt
