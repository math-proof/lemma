import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc_cutunbounded
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace SimpleGraph StatMech.Percolation StatMech StatMech.Walls


/--
[bc_cutUnbounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutunbounded.lean)
-/
@[path]
private lemma bc_cutUnbounded_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) x y := by
-- proof
  apply StatMech.Walls.bc_cutUnbounded ω x hinf n

/--
[bc_cutUnbounded_eq_crr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutunbounded.lean)
-/
@[path]
private lemma bc_cutUnbounded_eq_crr_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  bc_cutUnbounded ω x hinf n = crr_removeSite_infinite_reaches_far ω x hinf n := by
-- proof
  apply StatMech.Walls.bc_cutUnbounded_eq_crr ω x hinf n

/--
[bc_cutUnbounded_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutunbounded.lean)
-/
@[path]
private lemma bc_cutUnbounded_coord_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d (removeSite 0 ω) x y := by
-- proof
  apply StatMech.Walls.bc_cutUnbounded_coord ω x hinf n

/--
[bc_cutUnbounded_converse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutunbounded.lean)
-/
@[path]
private lemma bc_cutUnbounded_converse_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (h : ∀ n : ℕ, ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) x y) :
-- imply
  (cluster d (removeSite 0 ω) x).Infinite := by
-- proof
  apply StatMech.Walls.bc_cutUnbounded_converse ω x h

/--
[bc_cutUnbounded_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutunbounded.lean)
-/
@[path]
private lemma bc_cutUnbounded_iff_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  (cluster d (removeSite 0 ω) x).Infinite ↔ ∀ n : ℕ, ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) x y := by
-- proof
  apply StatMech.Walls.bc_cutUnbounded_iff ω x


-- created on 2026-10-23
