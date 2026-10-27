import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bkm_dccaxiscorridor
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bkm_axisCorridor_step_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccaxiscorridor.lean)
-/
@[path]
private lemma bkm_axisCorridor_step_open_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {s : ℕ}
-- given
  (h0 : 1 ≤ s)
  (hsL : s < L) :
-- imply
  IsOpenEdge d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j L) ω)) (hrHD_rayPt j (s : ℤ)) (hrHD_rayPt j ((s : ℤ) + 1)) := by
-- proof
  apply StatMech.Walls.bkm_axisCorridor_step_open ω j L s h0 hsL

/--
[bkm_axisCorridor_connected_to](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccaxiscorridor.lean)
-/
@[path]
private lemma bkm_axisCorridor_connected_to_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {m : ℕ}
-- given
  (hm1 : 1 ≤ m)
  (hmL : m ≤ L) :
-- imply
  Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j L) ω)) (hrHD_rayPt j 1) (hrHD_rayPt j (m : ℤ)) := by
-- proof
  apply StatMech.Walls.bkm_axisCorridor_connected_to ω j L m hm1 hmL

/--
[bkm_axisCorridor_survives_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccaxiscorridor.lean)
-/
@[path]
private lemma bkm_axisCorridor_survives_removeSite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j L) ω)) (hrHD_rayPt j 1) (hrHD_rayPt j (L : ℤ)) := by
-- proof
  apply StatMech.Walls.bkm_axisCorridor_survives_removeSite ω j L hL

/--
[bkm_farEnd_ne_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccaxiscorridor.lean)
-/
@[path]
private lemma bkm_farEnd_ne_origin_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  (hrHD_rayPt j (L : ℤ) : Site d) ≠ 0 := by
-- proof
  apply StatMech.Walls.bkm_farEnd_ne_origin j L hL

/--
[bkm_farEnd_ne_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccaxiscorridor.lean)
-/
@[path]
private lemma bkm_farEnd_ne_neighbour_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
-- given
  (hL : 2 ≤ L) :
-- imply
  (hrHD_rayPt j (L : ℤ) : Site d) ≠ hrHD_rayPt j 1 := by
-- proof
  apply StatMech.Walls.bkm_farEnd_ne_neighbour j L hL


-- created on 2026-10-23
