import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.WindingAnchorClose
open Finset Set SimpleGraph StatMech StatMech.Ising


/--
[wac_cycle_length_le_contourLen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/WindingAnchorClose.lean)
-/
@[path]
private lemma wac_cycle_length_le_contourLen_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {S : Set (Site 2)}
  {n : ℕ}
  {u : Site 2}
  {c : (faceBoundaryGraph S).Walk u u}
-- given
  (hSbox : S ⊆ box 2 n)
  (hcyc : c.IsCycle) :
-- imply
  c.length ≤ contourLen S (bondFinsetTouch 2 n) := by
-- proof
  apply StatMech.Ising.wac_cycle_length_le_contourLen hSbox c hcyc

/--
[wac_exitFaceUp_eq_axisVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/WindingAnchorClose.lean)
-/
@[path]
private lemma wac_exitFaceUp_eq_axisVertex_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  exitFaceUp (ω := ω) hfin = axisVertex 2 (exitIndex (ω := ω) hfin) := by
-- proof
  apply StatMech.Ising.wac_exitFaceUp_eq_axisVertex hfin

/--
[wac_axisVertex_coord0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/WindingAnchorClose.lean)
-/
@[path]
private lemma wac_axisVertex_coord0_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {j : ℕ} :
-- imply
  (axisVertex 2 j) 0 = (j : ℤ) := by
-- proof
  apply StatMech.Ising.wac_axisVertex_coord0 j

/--
[wac_lt_length_of_leftFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/WindingAnchorClose.lean)
-/
@[path]
private lemma wac_lt_length_of_leftFace_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {j : ℕ}
  {c : (faceBoundaryGraph K).Walk (axisVertex 2 j) (axisVertex 2 j)}
  {w : Site 2}
-- given
  (hcyc : c.IsCycle)
  (hwsup : w ∈ c.support)
  (hw0 : w 0 ≤ 0) :
-- imply
  j < c.length := by
-- proof
  apply StatMech.Ising.wac_lt_length_of_leftFace c hcyc hwsup hw0

/--
[wac_axisAnchor_of_windingCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/WindingAnchorClose.lean)
-/
@[path]
private lemma wac_axisAnchor_of_windingCycle_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {S : Set (Site 2)}
  {n : ℕ}
  {j : ℕ}
  {c : (faceBoundaryGraph S).Walk (axisVertex 2 j) (axisVertex 2 j)}
  {w : Site 2}
-- given
  (hSbox : S ⊆ box 2 n)
  (hfin : S.Finite)
  (hcyc : c.IsCycle)
  (hwsup : w ∈ c.support)
  (hw0 : w 0 ≤ 0) :
-- imply
  ∃ (T : Finset (Site 2)) (j' : ℕ), (faceBoundaryGraph S).support ⊆ (T : Set (Site 2)) ∧ j' < contourLen S (bondFinsetTouch 2 n) ∧ axisVertex 2 j' ∈ T := by
-- proof
  apply StatMech.Ising.wac_axisAnchor_of_windingCycle hSbox hfin c hcyc hwsup hw0

/--
[wac_axisAnchor_of_exitDartWinds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/WindingAnchorClose.lean)
-/
@[path]
private lemma wac_axisAnchor_of_exitDartWinds_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hwind : acc_ExitDartWinds ω hfin) :
-- imply
  ∃ (n : ℕ) (T : Finset (Site 2)) (j : ℕ), (faceBoundaryGraph (cluster 2 ω (origin 2))).support ⊆ (T : Set (Site 2)) ∧ j < contourLen (cluster 2 ω (origin 2)) (bondFinsetTouch 2 n) ∧ axisVertex 2 j ∈ T := by
-- proof
  apply StatMech.Ising.wac_axisAnchor_of_exitDartWinds hfin hwind

/--
[wac_unitCell_base_eq_axisVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/WindingAnchorClose.lean)
-/
@[path]
private lemma wac_unitCell_base_eq_axisVertex_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  dartFace ucBase.1 = axisVertex 2 0 := by
-- proof
  apply StatMech.Ising.wac_unitCell_base_eq_axisVertex

/--
[wac_unitCell_axisAnchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/WindingAnchorClose.lean)
-/
@[path]
private lemma wac_unitCell_axisAnchor_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ∃ (T : Finset (Site 2)) (j : ℕ), (faceBoundaryGraph unitCell).support ⊆ (T : Set (Site 2)) ∧ j < contourLen unitCell (bondFinsetTouch 2 0) ∧ axisVertex 2 j ∈ T := by
-- proof
  apply StatMech.Ising.wac_unitCell_axisAnchor


-- created on 2026-10-23
