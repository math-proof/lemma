import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc3_forcedcorridorarm.Part2
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc3_corridorArm_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_forcedcorridorarm.lean)
-/
@[path]
private lemma bc3_corridorArm_chain_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
  {G : Finset (Sym2 (Site d))}
-- given
  (hsub : hrHD_corridorEdges j (L + 1) ⊆ G) :
-- imply
  Relation.ReflTransGen (CorridorStep G) (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) := by
-- proof
  apply StatMech.Walls.bc3_corridorArm_chain j L G hsub

/--
[bc3_corridorArm_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_forcedcorridorarm.lean)
-/
@[path]
private lemma bc3_corridorArm_infinite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {G : Finset (Sym2 (Site d))}
-- given
  (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j ((L : ℤ) + 1))).Infinite) :
-- imply
  (cluster d (removeSite 0 (forceOpenFinset G ω)) (hrHD_rayPt j ((L : ℤ) + 1))).Infinite := by
-- proof
  apply StatMech.Walls.bc3_corridorArm_infinite ω j L G hinf

/--
[bc3_forcedCorridorArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_forcedcorridorarm.lean)
-/
@[path]
private lemma bc3_forcedCorridorArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {G : Finset (Sym2 (Site d))}
-- given
  (hsub : hrHD_corridorEdges j (L + 1) ⊆ G)
  (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j ((L : ℤ) + 1))).Infinite) :
-- imply
  bc3_ForcedCorridorArm ω j L G := by
-- proof
  apply StatMech.Walls.bc3_forcedCorridorArm ω j L G hsub hinf

/--
[bc3_three_corridorArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_forcedcorridorarm.lean)
-/
@[path]
private lemma bc3_three_corridorArms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ}
-- given
  (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((L₁ : ℤ) + 1))).Infinite)
  (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((L₂ : ℤ) + 1))).Infinite)
  (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((L₃ : ℤ) + 1))).Infinite) :
-- imply
  bc3_ForcedCorridorArm ω j₁ L₁ (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪ hrHD_corridorEdges j₃ (L₃ + 1)) ∧ bc3_ForcedCorridorArm ω j₂ L₂ (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪ hrHD_corridorEdges j₃ (L₃ + 1)) ∧ bc3_ForcedCorridorArm ω j₃ L₃ (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪ hrHD_corridorEdges j₃ (L₃ + 1)) := by
-- proof
  apply StatMech.Walls.bc3_three_corridorArms ω j₁ j₂ j₃ L₁ L₂ L₃ hi1 hi2 hi3

/--
[bc3_corridorArm_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_forcedcorridorarm.lean)
-/
@[path]
private lemma bc3_corridorArm_self_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j ((L : ℤ) + 1))).Infinite) :
-- imply
  bc3_ForcedCorridorArm ω j L (hrHD_corridorEdges j (L + 1)) := by
-- proof
  apply StatMech.Walls.bc3_corridorArm_self ω j L hinf

/--
[bc3_forcedCorridorArm_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_forcedcorridorarm.lean)
-/
@[path]
private lemma bc3_forcedCorridorArm_ne_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  (hrHD_rayPt j ((L : ℤ) + 1) : Site d) ≠ hrHD_rayPt j 1 := by
-- proof
  apply StatMech.Walls.bc3_forcedCorridorArm_ne j L hL


-- created on 2026-10-23
