import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc_wiringforcesopen
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc_wiring_forces_open_eq_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_wiringforcesopen.lean)
-/
@[path]
private lemma bc_wiring_forces_open_eq_true_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L t : ℕ}
-- given
  (ht : t < L) :
-- imply
  forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true := by
-- proof
  apply StatMech.Walls.bc_wiring_forces_open_eq_true ω j L t ht

/--
[bc_wiring_forces_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_wiringforcesopen.lean)
-/
@[path]
private lemma bc_wiring_forces_open_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L t : ℕ}
-- given
  (ht : t < L) :
-- imply
  IsOpenEdge d (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) (hrHD_rayPt j ((t : ℤ) + 1)) (hrHD_rayPt j ((t : ℤ) + 2)) := by
-- proof
  apply StatMech.Walls.bc_wiring_forces_open ω j L t ht

/--
[bc_wiring_forces_open_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_wiringforcesopen.lean)
-/
@[path]
private lemma bc_wiring_forces_open_all_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ} :
-- imply
  ∀ t : ℕ, t < L → IsOpenEdge d (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) (hrHD_rayPt j ((t : ℤ) + 1)) (hrHD_rayPt j ((t : ℤ) + 2)) := by
-- proof
  apply StatMech.Walls.bc_wiring_forces_open_all ω j L


-- created on 2026-10-23
