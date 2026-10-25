import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc6stepsameray
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc6_mem_clusterNbhd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6stepsameray.lean)
-/
@[path]
private lemma bc6_mem_clusterNbhd_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {x : Site d} :
-- imply
  x ∈ bc6_clusterNbhd ω j L ↔ ∃ t : ℕ, (1 ≤ t ∧ t ≤ L) ∧ x ∈ cluster d (removeSite 0 ω) (hrHD_rayPt j (t : ℤ)) := by
-- proof
  apply StatMech.Walls.bc6_mem_clusterNbhd

/--
[bc6_rayPt_mem_clusterNbhd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6stepsameray.lean)
-/
@[path]
private lemma bc6_rayPt_mem_clusterNbhd_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L t : ℕ}
-- given
  (h0 : 1 ≤ t)
  (h1 : t ≤ L) :
-- imply
  hrHD_rayPt j (t : ℤ) ∈ bc6_clusterNbhd ω j L := by
-- proof
  apply StatMech.Walls.bc6_rayPt_mem_clusterNbhd h0 h1

/--
[bc6_corridorEdge_structure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6stepsameray.lean)
-/
@[path]
private lemma bc6_corridorEdge_structure_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
  {u v : Site d}
-- given
  (h : s(u, v) ∈ hrHD_corridorEdges j L) :
-- imply
  ∃ p : ℕ, p < L ∧ s(u, v) = s(hrHD_rayPt j (p : ℤ), hrHD_rayPt j ((p : ℤ) + 1)) := by
-- proof
  apply StatMech.Walls.bc6_corridorEdge_structure h

/--
[bc6_sameAxis_step_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6stepsameray.lean)
-/
@[path]
private lemma bc6_sameAxis_step_mem_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a : Fin d}
  {La : ℕ}
  {u v : Site d}
-- given
  (hno0 : (0 : Site d) ∉ s(u, v))
  (hmem : s(u, v) ∈ hrHD_corridorEdges a (La + 1)) :
-- imply
  v ∈ bc6_clusterNbhd ω a (La + 1) := by
-- proof
  apply StatMech.Walls.bc6_sameAxis_step_mem ω a La hno0 hmem


-- created on 2026-10-23
