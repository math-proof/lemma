import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bkm_dccstepopen
open Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bkm_dcc_step_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccstepopen.lean)
-/
@[path]
private lemma bkm_dcc_step_open_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj x y)
  (hmem : s(x, y) ∈ G)
  (h0 : (0 : Site d) ∉ s(x, y)) :
-- imply
  StatMech.Lattice.IsOpenEdge d (StatMech.Percolation.removeSite 0 (StatMech.Percolation.forceOpenFinset G ω)) x y := by
-- proof
  apply StatMech.Walls.bkm_dcc_step_open ω G hadj hmem h0

/--
[bkm_dcc_step_open_eq_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccstepopen.lean)
-/
@[path]
private lemma bkm_dcc_step_open_eq_true_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hmem : s(x, y) ∈ G)
  (h0 : (0 : Site d) ∉ s(x, y)) :
-- imply
  StatMech.Percolation.removeSite 0 (StatMech.Percolation.forceOpenFinset G ω) s(x, y) = true := by
-- proof
  apply StatMech.Walls.bkm_dcc_step_open_eq_true ω G hmem h0


-- created on 2026-10-23
