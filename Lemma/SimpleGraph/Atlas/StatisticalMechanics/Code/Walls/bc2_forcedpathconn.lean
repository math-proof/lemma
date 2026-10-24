import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc2_forcedpathconn
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc2_forcedPath_connected_of_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcedpathconn.lean)
-/
@[path]
private lemma bc2_forcedPath_connected_of_chain_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {p q : Site d}
-- given
  (h : Relation.ReflTransGen (CorridorStep W) p q) :
-- imply
  Connected d (removeSite 0 (forceOpenFinset W ω)) p q := by
-- proof
  apply StatMech.Walls.bc2_forcedPath_connected_of_chain ω W h

/--
[bc2_corridorStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcedpathconn.lean)
-/
@[path]
private lemma bc2_corridorStep_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
  {s : ℕ}
-- given
  (h0 : 1 ≤ s)
  (hsL : s ≤ L) :
-- imply
  CorridorStep (hrHD_corridorEdges j (L + 1)) (hrHD_rayPt j (s : ℤ)) (hrHD_rayPt j ((s : ℤ) + 1)) := by
-- proof
  apply StatMech.Walls.bc2_corridorStep j L s h0 hsL

/--
[bc2_corridorChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcedpathconn.lean)
-/
@[path]
private lemma bc2_corridorChain_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
  {m : ℕ}
-- given
  (hm1 : 1 ≤ m)
  (hmL : m ≤ L + 1) :
-- imply
  Relation.ReflTransGen (CorridorStep (hrHD_corridorEdges j (L + 1))) (hrHD_rayPt j 1) (hrHD_rayPt j (m : ℤ)) := by
-- proof
  apply StatMech.Walls.bc2_corridorChain j L m hm1 hmL

/--
[bc2_forcedPathConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcedpathconn.lean)
-/
@[path]
private lemma bc2_forcedPathConn_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {m : ℕ}
-- given
  (hm1 : 1 ≤ m)
  (hmL : m ≤ L + 1) :
-- imply
  Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)) (hrHD_rayPt j 1) (hrHD_rayPt j (m : ℤ)) := by
-- proof
  apply StatMech.Walls.bc2_forcedPathConn ω j L m hm1 hmL

/--
[bc2_forcedPathConn_farEnd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcedpathconn.lean)
-/
@[path]
private lemma bc2_forcedPathConn_farEnd_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ} :
-- imply
  Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)) (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) := by
-- proof
  apply StatMech.Walls.bc2_forcedPathConn_farEnd ω j L

/--
[bc2_corridorMouth_forced_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcedpathconn.lean)
-/
@[path]
private lemma bc2_corridorMouth_forced_open_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L t : ℕ}
-- given
  (ht : t < L) :
-- imply
  IsOpenEdge d (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) (hrHD_rayPt j ((t : ℤ) + 1)) (hrHD_rayPt j ((t : ℤ) + 2)) := by
-- proof
  apply StatMech.Walls.bc2_corridorMouth_forced_open ω j L t ht

/--
[bc2_corridorChain_one_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcedpathconn.lean)
-/
@[path]
private lemma bc2_corridorChain_one_step_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  CorridorStep (hrHD_corridorEdges j (L + 1)) (hrHD_rayPt j 1) (hrHD_rayPt j 2) := by
-- proof
  apply StatMech.Walls.bc2_corridorChain_one_step j L hL

/--
[bc2_farEnd_ne_mouth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_forcedpathconn.lean)
-/
@[path]
private lemma bc2_farEnd_ne_mouth_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  (hrHD_rayPt j ((L : ℤ) + 1) : Site d) ≠ hrHD_rayPt j 1 := by
-- proof
  apply StatMech.Walls.bc2_farEnd_ne_mouth j L hL


-- created on 2026-10-23
