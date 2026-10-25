import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.PcFarContour
open Finset Set SimpleGraph Function StatMech StatMech.Percolation


/--
[pcFar_exitDartsSameOrbit_of_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcFarContour.lean)
-/
@[path]
private lemma pcFar_exitDartsSameOrbit_of_far_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
  (hfar : pcFar_ExitHeadsFar ω hfin) :
-- imply
  ExitDartsSameOrbit ω hfin := by
-- proof
  apply StatMech.Percolation.pcFar_exitDartsSameOrbit_of_far hfin hInt hfar

/--
[pcFar_cycleHasLeftFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcFarContour.lean)
-/
@[path]
private lemma pcFar_cycleHasLeftFace_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hsimple : OrbitFaceSimple ω hfin)
  (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
  (hfar : pcFar_ExitHeadsFar ω hfin) :
-- imply
  CycleHasLeftFace ω hfin := by
-- proof
  apply StatMech.Percolation.pcFar_cycleHasLeftFace hfin hsimple hInt hfar

/--
[pcFar_cycleHasLeftFace_of_noPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcFarContour.lean)
-/
@[path]
private lemma pcFar_cycleHasLeftFace_of_noPinch_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
  (hnoPinch : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
  (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
  (hfar : pcFar_ExitHeadsFar ω hfin) :
-- imply
  CycleHasLeftFace ω hfin := by
-- proof
  apply StatMech.Percolation.pcFar_cycleHasLeftFace_of_noPinch hfin hp hnoPinch hInt hfar

/--
[pcFar_pcAnchoredEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcFarContour.lean)
-/
@[path]
private lemma pcFar_pcAnchoredEnclosure_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), OrbitFaceSimple ω hfin ∧ InterfaceConnected (cluster 2 ω (origin 2)) ∧ pcFar_ExitHeadsFar ω hfin) :
-- imply
  PcAnchoredEnclosure := by
-- proof
  apply StatMech.Percolation.pcFar_pcAnchoredEnclosure h

/--
[pcFar_pc_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcFarContour.lean)
-/
@[path]
private lemma pcFar_pc_lt_one_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), OrbitFaceSimple ω hfin ∧ InterfaceConnected (cluster 2 ω (origin 2)) ∧ pcFar_ExitHeadsFar ω hfin) :
-- imply
  pc 2 < 1 := by
-- proof
  apply StatMech.Percolation.pcFar_pc_lt_one h

/--
[pcFar_pc_pos_and_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcFarContour.lean)
-/
@[path]
private lemma pcFar_pc_pos_and_lt_one_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), OrbitFaceSimple ω hfin ∧ InterfaceConnected (cluster 2 ω (origin 2)) ∧ pcFar_ExitHeadsFar ω hfin) :
-- imply
  0 < pc 2 ∧ pc 2 < 1 := by
-- proof
  apply StatMech.Percolation.pcFar_pc_pos_and_lt_one h


-- created on 2026-10-23
