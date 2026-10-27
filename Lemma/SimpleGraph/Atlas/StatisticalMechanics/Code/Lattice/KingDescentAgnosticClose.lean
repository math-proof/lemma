import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.KingDescentAgnosticClose.Part2
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[kda_stairDR_raycount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_stairDR_raycount_eq
  {z : Site 2} :
-- imply
  jec_rayCount z kda_stairDR = (if 0 ≤ z 0 - 1 ∧ 1 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 1 + (2:ℤ) - 1 then 1 else 0) + (if 3 ≤ z 0 - 1 ∧ 2 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 2 + (1:ℤ) - 1 then 1 else 0) + (if 4 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (2:ℤ) - 1 then 1 else 0) + (if 2 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (1:ℤ) - 1 then 1 else 0) := by
-- proof
  apply StatMech.Lattice.kda_stairDR_raycount z

/--
[kda_stairDR_support_locus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_stairDR_support_locus_eq
  {p : Site 2}
-- given
  (hp : p ∈ kda_stairDR.support) :
-- imply
  (p 0 = 0 ∧ 1 ≤ p 1 ∧ p 1 ≤ 3) ∨ (p 1 = 3 ∧ 0 ≤ p 0 ∧ p 0 ≤ 3) ∨ (p 0 = 3 ∧ 2 ≤ p 1 ∧ p 1 ≤ 3) ∨ (p 1 = 2 ∧ 3 ≤ p 0 ∧ p 0 ≤ 4) ∨ (p 0 = 4 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2) ∨ (p 1 = 0 ∧ 2 ≤ p 0 ∧ p 0 ≤ 4) ∨ (p 0 = 2 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1) ∨ (p 1 = 1 ∧ 0 ≤ p 0 ∧ p 0 ≤ 2) := by
-- proof
  apply StatMech.Lattice.kda_stairDR_support_locus p hp

/--
[kda_off_12](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_off_12_eq :
-- imply
  (![1, 2] : Site 2) ∉ kda_stairDR.support := by
-- proof
  apply StatMech.Lattice.kda_off_12

/--
[kda_off_22](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_off_22_eq :
-- imply
  (![2, 2] : Site 2) ∉ kda_stairDR.support := by
-- proof
  apply StatMech.Lattice.kda_off_22

/--
[kda_off_31](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_off_31_eq :
-- imply
  (![3, 1] : Site 2) ∉ kda_stairDR.support := by
-- proof
  apply StatMech.Lattice.kda_off_31

/--
[kda_on_02](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_on_02_eq :
-- imply
  (![0, 2] : Site 2) ∈ kda_stairDR.support := by
-- proof
  apply StatMech.Lattice.kda_on_02

/--
[kda_on_23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_on_23_eq :
-- imply
  (![2, 3] : Site 2) ∈ kda_stairDR.support := by
-- proof
  apply StatMech.Lattice.kda_on_23

/--
[kda_on_32](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_on_32_eq :
-- imply
  (![3, 2] : Site 2) ∈ kda_stairDR.support := by
-- proof
  apply StatMech.Lattice.kda_on_32

/--
[kda_on_21](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_on_21_eq :
-- imply
  (![2, 1] : Site 2) ∈ kda_stairDR.support := by
-- proof
  apply StatMech.Lattice.kda_on_21

/--
[kda_on_11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_on_11_eq :
-- imply
  (![1, 1] : Site 2) ∈ kda_stairDR.support := by
-- proof
  apply StatMech.Lattice.kda_on_11

/--
[kda_on_01](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_on_01_eq :
-- imply
  (![0, 1] : Site 2) ∈ kda_stairDR.support := by
-- proof
  apply StatMech.Lattice.kda_on_01

/--
[kda_interior_12](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_interior_12_eq :
-- imply
  (![1, 2] : Site 2) ∈ jec_leftRegion kda_stairDR := by
-- proof
  apply StatMech.Lattice.kda_interior_12

/--
[kda_interior_22](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_interior_22_eq :
-- imply
  (![2, 2] : Site 2) ∈ jec_leftRegion kda_stairDR := by
-- proof
  apply StatMech.Lattice.kda_interior_22

/--
[kda_interior_31](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_interior_31_eq :
-- imply
  (![3, 1] : Site 2) ∈ jec_leftRegion kda_stairDR := by
-- proof
  apply StatMech.Lattice.kda_interior_31

/--
[kda_mem_interior_12](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_mem_interior_12_eq :
-- imply
  (![1, 2] : Site 2) ∈ jil_offSupportInterior kda_stairDR := by
-- proof
  apply StatMech.Lattice.kda_mem_interior_12

/--
[kda_mem_interior_22](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_mem_interior_22_eq :
-- imply
  (![2, 2] : Site 2) ∈ jil_offSupportInterior kda_stairDR := by
-- proof
  apply StatMech.Lattice.kda_mem_interior_22

/--
[kda_mem_interior_31](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_mem_interior_31_eq :
-- imply
  (![3, 1] : Site 2) ∈ jil_offSupportInterior kda_stairDR := by
-- proof
  apply StatMech.Lattice.kda_mem_interior_31

/--
[kda_on_33](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_on_33_eq :
-- imply
  (![3, 3] : Site 2) ∈ kda_stairDR.support := by
-- proof
  apply StatMech.Lattice.kda_on_33

/--
[kda_on_13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_on_13_eq :
-- imply
  (![1, 3] : Site 2) ∈ kda_stairDR.support := by
-- proof
  apply StatMech.Lattice.kda_on_13

/--
[kda_on_41](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_on_41_eq :
-- imply
  (![4, 1] : Site 2) ∈ kda_stairDR.support := by
-- proof
  apply StatMech.Lattice.kda_on_41

/--
[kda_on_42](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_on_42_eq :
-- imply
  (![4, 2] : Site 2) ∈ kda_stairDR.support := by
-- proof
  apply StatMech.Lattice.kda_on_42

/--
[kda_interior_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_interior_eq_eq :
-- imply
  jil_offSupportInterior kda_stairDR = {(![1, 2] : Site 2), (![2, 2] : Site 2), (![3, 1] : Site 2)} := by
-- proof
  apply StatMech.Lattice.kda_interior_eq

/--
[kda_support_cells](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_support_cells_eq
  {p : Site 2}
-- given
  (hp : p ∈ kda_stairDR.support) :
-- imply
  p = (![0,1]:Site 2) ∨ p = (![0,2]:Site 2) ∨ p = (![0,3]:Site 2) ∨ p = (![1,3]:Site 2) ∨ p = (![2,3]:Site 2) ∨ p = (![3,3]:Site 2) ∨ p = (![3,2]:Site 2) ∨ p = (![4,2]:Site 2) ∨ p = (![4,1]:Site 2) ∨ p = (![4,0]:Site 2) ∨ p = (![3,0]:Site 2) ∨ p = (![2,0]:Site 2) ∨ p = (![2,1]:Site 2) ∨ p = (![1,1]:Site 2) := by
-- proof
  apply StatMech.Lattice.kda_support_cells p hp

/--
[kda_stairDR_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_stairDR_fourThin_eq :
-- imply
  mci_FourThin kda_stairDR := by
-- proof
  apply StatMech.Lattice.kda_stairDR_fourThin

/--
[kda_kingAdj_downLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_kingAdj_downLeft_eq
  {x y : ℤ} :
-- imply
  mci_kingGraph.Adj (![x, y] : Site 2) ![x - 1, y - 1] := by
-- proof
  apply StatMech.Lattice.kda_kingAdj_downLeft x y

/--
[kda_kingAdj_downRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_kingAdj_downRight_eq
  {x y : ℤ} :
-- imply
  mci_kingGraph.Adj (![x, y] : Site 2) ![x + 1, y - 1] := by
-- proof
  apply StatMech.Lattice.kda_kingAdj_downRight x y

/--
[kda_descentStep_to_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_descentStep_to_neighbour_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {M : ℤ}
  {x y : ℤ}
  {w : Site 2}
-- given
  (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hw : w ∈ jil_offSupportInterior Vc)
  (hadj : mci_kingGraph.Adj (![x, y] : Site 2) w)
  (hlex : w 1 < y ∨ (w 1 = y ∧ w 0 < x)) :
-- imply
  ∃ z' ∈ jil_offSupportInterior Vc, rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧ ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z', ∀ u ∈ p.support, u ∈ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.kda_descentStep_to_neighbour Vc M hMb hz hw hadj hlex

/--
[kda_kingDownLink_of_descentStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_kingDownLink_of_descentStep_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {M : ℤ}
-- given
  (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hres : kda_KingDescentStep Vc seed) :
-- imply
  kif_KingDownLink Vc seed M := by
-- proof
  apply StatMech.Lattice.kda_kingDownLink_of_descentStep Vc M hMb hres

/--
[kda_kingRowLinked_of_descentStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_kingRowLinked_of_descentStep_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {M : ℤ}
-- given
  (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hres : kda_KingDescentStep Vc seed) :
-- imply
  mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.kda_kingRowLinked_of_descentStep Vc M hMb hres

/--
[kda_seed_is_31](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_seed_is_31_eq
  {M : ℤ}
  {seed : Site 2}
-- given
  (hMb : ∀ z ∈ jec_leftRegion kda_stairDR, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hseed : seed ∈ jil_offSupportInterior kda_stairDR)
  (hmin : ∀ z ∈ jil_offSupportInterior kda_stairDR, rlc_lexMeasure M seed ≤ rlc_lexMeasure M z) :
-- imply
  seed = (![3, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.kda_seed_is_31 hMb hseed hmin

/--
[kda_stairDR_descentStep_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_stairDR_descentStep_false_eq :
-- imply
  ¬ kda_KingDescentStep kda_stairDR (![3, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.kda_stairDR_descentStep_false

/--
[kda_descentStep_lexMinSeed_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_descentStep_lexMinSeed_false_eq :
-- imply
  ∃ seed : Site 2, seed ∈ jil_offSupportInterior kda_stairDR ∧ ¬ kda_KingDescentStep kda_stairDR seed := by
-- proof
  apply StatMech.Lattice.kda_descentStep_lexMinSeed_false

/--
[kda_stairDR_kingRowLinked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_stairDR_kingRowLinked_eq :
-- imply
  mci_KingRowLinked kda_stairDR (![3, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.kda_stairDR_kingRowLinked

/--
[kda_descentStep_false_but_theorem_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingDescentAgnosticClose.lean)
-/
@[path]
private lemma kda_descentStep_false_but_theorem_true_eq :
-- imply
  mci_FourThin kda_stairDR ∧ mci_KingRowLinked kda_stairDR (![3, 1] : Site 2) ∧ ¬ kda_KingDescentStep kda_stairDR (![3, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.kda_descentStep_false_but_theorem_true


-- created on 2026-10-23
