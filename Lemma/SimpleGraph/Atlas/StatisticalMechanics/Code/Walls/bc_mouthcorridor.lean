import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc_mouthcorridor
open Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc_mouthCorridor_step_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_mouthcorridor.lean)
-/
@[path]
private lemma bc_mouthCorridor_step_open_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {s : ℕ}
-- given
  (h0 : 1 ≤ s)
  (hsL : s ≤ L) :
-- imply
  IsOpenEdge d (bc_mouthCutConfig j L ω) (hrHD_rayPt j (s : ℤ)) (hrHD_rayPt j ((s : ℤ) + 1)) := by
-- proof
  apply StatMech.Walls.bc_mouthCorridor_step_open ω j L s h0 hsL

/--
[bc_mouthCorridor_connected_to](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_mouthcorridor.lean)
-/
@[path]
private lemma bc_mouthCorridor_connected_to_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {m : ℕ}
-- given
  (hm1 : 1 ≤ m)
  (hmL : m ≤ L + 1) :
-- imply
  Connected d (bc_mouthCutConfig j L ω) (hrHD_rayPt j 1) (hrHD_rayPt j (m : ℤ)) := by
-- proof
  apply StatMech.Walls.bc_mouthCorridor_connected_to ω j L m hm1 hmL

/--
[bc_mouthCorridor_reaches_farEnd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_mouthcorridor.lean)
-/
@[path]
private lemma bc_mouthCorridor_reaches_farEnd_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ} :
-- imply
  Connected d (bc_mouthCutConfig j L ω) (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) := by
-- proof
  apply StatMech.Walls.bc_mouthCorridor_reaches_farEnd ω j L

/--
[bc_corridorCell_ne_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_mouthcorridor.lean)
-/
@[path]
private lemma bc_corridorCell_ne_origin_eq
  {d : ℕ}
  {j : Fin d}
  {m : ℕ}
-- given
  (hm : 1 ≤ m) :
-- imply
  (hrHD_rayPt j (m : ℤ) : Site d) ≠ 0 := by
-- proof
  apply StatMech.Walls.bc_corridorCell_ne_origin j m hm

/--
[bc_farEnd_ne_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_mouthcorridor.lean)
-/
@[path]
private lemma bc_farEnd_ne_neighbour_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  (hrHD_rayPt j ((L : ℤ) + 1) : Site d) ≠ hrHD_rayPt j 1 := by
-- proof
  apply StatMech.Walls.bc_farEnd_ne_neighbour j L hL


-- created on 2026-10-23
