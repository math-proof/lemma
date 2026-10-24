import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc_cutsomeaxis
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc_exists_far_axis_of_notMem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutsomeaxis.lean)
-/
@[path]
private lemma bc_exists_far_axis_of_notMem_box_eq
  {d : ℕ}
  {y : Site d}
  {n : ℕ}
-- given
  (hyb : y ∉ box d n) :
-- imply
  ∃ i : Fin d, n < (y i).natAbs := by
-- proof
  apply StatMech.Walls.bc_exists_far_axis_of_notMem_box hyb

/--
[bc_cut_some_axis_of_far_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutsomeaxis.lean)
-/
@[path]
private lemma bc_cut_some_axis_of_far_witness_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {y : Site d}
  {n : ℕ}
-- given
  (hyb : y ∉ box d n)
  (hyc : Connected d (removeSite 0 ω) x y) :
-- imply
  ∃ z, (∃ i : Fin d, n < (z i).natAbs) ∧ Connected d (removeSite 0 ω) x z := by
-- proof
  apply StatMech.Walls.bc_cut_some_axis_of_far_witness ω x hyb hyc

/--
[bc_cut_reaches_far_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutsomeaxis.lean)
-/
@[path]
private lemma bc_cut_reaches_far_coord_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d (removeSite 0 ω) x y := by
-- proof
  apply StatMech.Walls.bc_cut_reaches_far_coord ω x hinf n

/--
[bc_cut_some_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutsomeaxis.lean)
-/
@[path]
private lemma bc_cut_some_axis_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  ∀ n : ℕ, ∃ y, ∃ i : Fin d, n < (y i).natAbs ∧ Connected d (removeSite 0 ω) x y := by
-- proof
  apply StatMech.Walls.bc_cut_some_axis ω x hinf

/--
[bc_some_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutsomeaxis.lean)
-/
@[path]
private lemma bc_some_axis_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d ω x).Infinite) :
-- imply
  ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d ω x y := by
-- proof
  apply StatMech.Walls.bc_some_axis ω x hinf n


-- created on 2026-10-23
