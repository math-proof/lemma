import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc47aggregate.Part4
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc47_gatedSum_eq_sigma_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean)
-/
@[path]
private lemma gc47_gatedSum_eq_sigma_card_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {s : Finset (Finset ι)} :
-- imply
  (∑ M ∈ s, gc40_E ends M) = #(s.sigma (fun M => gc45_evenSub ends M)) := by
-- proof
  apply StatMech.Walls.gc47_gatedSum_eq_sigma_card ends s

/--
[gc47_LHSpairs_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean)
-/
@[path]
private lemma gc47_LHSpairs_card_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W} :
-- imply
  (∑ M ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x} : Finset W)), (if connK ends M x g then gc40_E ends M else 0)) = #(gc47_LHSpairs ends o x y g) := by
-- proof
  apply StatMech.Walls.gc47_LHSpairs_card ends o x y g

/--
[gc47_RHSpairs_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean)
-/
@[path]
private lemma gc47_RHSpairs_card_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W} :
-- imply
  (∑ M ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x, y, g} : Finset W)), (if connK ends M o x ∧ connK ends M o y ∧ connK ends M o g then gc40_E ends M else 0)) = #(gc47_RHSpairs ends o x y g) := by
-- proof
  apply StatMech.Walls.gc47_RHSpairs_card ends o x y g

/--
[gc47_EMassResidue_iff_pairCount_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean)
-/
@[path]
private lemma gc47_EMassResidue_iff_pairCount_le_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W} :
-- imply
  gc42_EMassResidue ends o x y g ↔ #(gc47_LHSpairs ends o x y g) ≤ #(gc47_RHSpairs ends o x y g) := by
-- proof
  apply StatMech.Walls.gc47_EMassResidue_iff_pairCount_le ends o x y g

/--
[gc47_EMassResidue_of_pairInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean)
-/
@[path]
private lemma gc47_EMassResidue_of_pairInjection_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (h : gc47_PairInjection ends o x y g) :
-- imply
  gc42_EMassResidue ends o x y g := by
-- proof
  apply StatMech.Walls.gc47_EMassResidue_of_pairInjection ends o x y g h

/--
[gc47_countIneq_of_pairInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean)
-/
@[path]
private lemma gc47_countIneq_of_pairInjection_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (h : gc47_PairInjection ends o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc47_countIneq_of_pairInjection ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc47_defect_LHSpairs_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean)
-/
@[path]
private lemma gc47_defect_LHSpairs_card_eq :
-- imply
  #(gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3) = 7 := by
-- proof
  apply StatMech.Walls.gc47_defect_LHSpairs_card

/--
[gc47_defect_RHSpairs_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean)
-/
@[path]
private lemma gc47_defect_RHSpairs_card_eq :
-- imply
  #(gc47_RHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3) = 7 := by
-- proof
  apply StatMech.Walls.gc47_defect_RHSpairs_card

/--
[gc47_defect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean)
-/
@[path]
private lemma gc47_defect_eq :
-- imply
  ∀ p ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3, gc47_defectΦ p ∈ gc47_RHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc47_defect

/--
[gc47_defect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean)
-/
@[path]
private lemma gc47_defect_eq_2 :
-- imply
  Set.InjOn gc47_defectΦ (gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3) := by
-- proof
  apply StatMech.Walls.gc47_defect

/--
[gc47_defect_pairInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean)
-/
@[path]
private lemma gc47_defect_pairInjection_eq :
-- imply
  gc47_PairInjection gc46_defectEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc47_defect_pairInjection

/--
[gc47_defect_EMassResidue_via_pairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean)
-/
@[path]
private lemma gc47_defect_EMassResidue_via_pairs_eq :
-- imply
  gc42_EMassResidue gc46_defectEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc47_defect_EMassResidue_via_pairs

/--
[gc47_defectOverflow_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean)
-/
@[path]
private lemma gc47_defectOverflow_card_eq :
-- imply
  #gc47_defectOverflow = 6 := by
-- proof
  apply StatMech.Walls.gc47_defectOverflow_card

/--
[gc47_defectOverflow_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean)
-/
@[path]
private lemma gc47_defectOverflow_subset_eq :
-- imply
  gc47_defectOverflow ⊆ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc47_defectOverflow_subset

/--
[gc47_defect_univFibre_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean)
-/
@[path]
private lemma gc47_defect_univFibre_card_eq :
-- imply
  #(({(univ : Finset (Fin 5))} : Finset (Finset (Fin 5))).sigma (fun M => gc45_evenSub gc46_defectEnds M)) = 4 := by
-- proof
  apply StatMech.Walls.gc47_defect_univFibre_card

/--
[gc47_defect_no_subset_pairInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean)
-/
@[path]
private lemma gc47_defect_no_subset_pairInjection_eq :
-- imply
  ¬ ∃ Φ : (Σ _ : Finset (Fin 5), Finset (Fin 5)) → (Σ _ : Finset (Fin 5), Finset (Fin 5)), (∀ p ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3, Φ p ∈ gc47_RHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3) ∧ Set.InjOn Φ (gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3) ∧ (∀ p ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3, p.1 ⊆ (Φ p).1) := by
-- proof
  apply StatMech.Walls.gc47_defect_no_subset_pairInjection

/--
[gc47_defect_pairLevel_splits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc47aggregate.lean)
-/
@[path]
private lemma gc47_defect_pairLevel_splits_eq :
-- imply
  gc47_PairInjection gc46_defectEnds (0 : Fin 4) 1 2 3 ∧ ¬ ∃ Φ : (Σ _ : Finset (Fin 5), Finset (Fin 5)) → (Σ _ : Finset (Fin 5), Finset (Fin 5)), (∀ p ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3, Φ p ∈ gc47_RHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3) ∧ Set.InjOn Φ (gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3) ∧ (∀ p ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3, p.1 ⊆ (Φ p).1) := by
-- proof
  apply StatMech.Walls.gc47_defect_pairLevel_splits


-- created on 2026-10-23
