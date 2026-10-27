import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc48pairinject.Part2
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc48_pairInjection_of_pairCount_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean)
-/
@[path]
private lemma gc48_pairInjection_of_pairCount_le_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (hcard : #(gc47_LHSpairs ends o x y g) ≤ #(gc47_RHSpairs ends o x y g)) :
-- imply
  gc47_PairInjection ends o x y g := by
-- proof
  apply StatMech.Walls.gc48_pairInjection_of_pairCount_le ends o x y g hcard

/--
[gc48_pairInjection_of_EMassResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean)
-/
@[path]
private lemma gc48_pairInjection_of_EMassResidue_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (h : gc42_EMassResidue ends o x y g) :
-- imply
  gc47_PairInjection ends o x y g := by
-- proof
  apply StatMech.Walls.gc48_pairInjection_of_EMassResidue ends o x y g h

/--
[gc48_pairInjection_iff_EMassResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean)
-/
@[path]
private lemma gc48_pairInjection_iff_EMassResidue_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W} :
-- imply
  gc47_PairInjection ends o x y g ↔ gc42_EMassResidue ends o x y g := by
-- proof
  apply StatMech.Walls.gc48_pairInjection_iff_EMassResidue ends o x y g

/--
[gc48_pairInjection_iff_pairCount_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean)
-/
@[path]
private lemma gc48_pairInjection_iff_pairCount_le_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W} :
-- imply
  gc47_PairInjection ends o x y g ↔ #(gc47_LHSpairs ends o x y g) ≤ #(gc47_RHSpairs ends o x y g) := by
-- proof
  apply StatMech.Walls.gc48_pairInjection_iff_pairCount_le ends o x y g

/--
[gc48_sigma_card_eq_doubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean)
-/
@[path]
private lemma gc48_sigma_card_eq_doubled_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {s : Finset (Finset ι)}
  [DecidablePred P]
-- given
  (P : Finset ι → Prop)
  (hs : ∀ M, M ∈ s ↔ M ⊆ univ ∧ P M) :
-- imply
  #(s.sigma (fun M => gc45_evenSub ends M)) = #((univ : Finset (Finset ι × Finset ι)).filter (fun p => p.2 ⊆ univ \ p.1 ∧ sources ends p.1 = (∅ : Finset W) ∧ P (p.1 ∪ p.2))) := by
-- proof
  apply StatMech.Walls.gc48_sigma_card_eq_doubled ends s P hs

/--
[gc48_union_sources_eq_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean)
-/
@[path]
private lemma gc48_union_sources_eq_snd_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {p : Finset ι × Finset ι}
-- given
  (hdisj : p.2 ⊆ univ \ p.1)
  (hn1 : sources ends p.1 = (∅ : Finset W)) :
-- imply
  sources ends (p.1 ∪ p.2) = sources ends p.2 := by
-- proof
  apply StatMech.Walls.gc48_union_sources_eq_snd ends hdisj hn1

/--
[gc48_LHSpairs_card_eq_doubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean)
-/
@[path]
private lemma gc48_LHSpairs_card_eq_doubled_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W} :
-- imply
  #(gc47_LHSpairs ends o x y g) = #(gc48_LHSdoubled ends o x y g) := by
-- proof
  apply StatMech.Walls.gc48_LHSpairs_card_eq_doubled ends o x y g

/--
[gc48_RHSpairs_card_eq_doubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean)
-/
@[path]
private lemma gc48_RHSpairs_card_eq_doubled_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W} :
-- imply
  #(gc47_RHSpairs ends o x y g) = #(gc48_RHSdoubled ends o x y g) := by
-- proof
  apply StatMech.Walls.gc48_RHSpairs_card_eq_doubled ends o x y g

/--
[gc48_EMassResidue_iff_doubled_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean)
-/
@[path]
private lemma gc48_EMassResidue_iff_doubled_le_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W} :
-- imply
  gc42_EMassResidue ends o x y g ↔ #(gc48_LHSdoubled ends o x y g) ≤ #(gc48_RHSdoubled ends o x y g) := by
-- proof
  apply StatMech.Walls.gc48_EMassResidue_iff_doubled_le ends o x y g

/--
[gc48_countIneq_of_pairCount_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean)
-/
@[path]
private lemma gc48_countIneq_of_pairCount_le_eq
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
  (hcard : #(gc47_LHSpairs ends o x y g) ≤ #(gc47_RHSpairs ends o x y g)) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc48_countIneq_of_pairCount_le ends hnd hox hoy hog hxy hxg hyg huniv hcard

/--
[gc48_defect_pairCount_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean)
-/
@[path]
private lemma gc48_defect_pairCount_le_eq :
-- imply
  #(gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3) ≤ #(gc47_RHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3) := by
-- proof
  apply StatMech.Walls.gc48_defect_pairCount_le

/--
[gc48_defect_pairInjection_via_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean)
-/
@[path]
private lemma gc48_defect_pairInjection_via_count_eq :
-- imply
  gc47_PairInjection gc46_defectEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc48_defect_pairInjection_via_count

/--
[gc48_defect_LHSdoubled_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean)
-/
@[path]
private lemma gc48_defect_LHSdoubled_card_eq :
-- imply
  #(gc48_LHSdoubled gc46_defectEnds (0 : Fin 4) 1 2 3) = 7 := by
-- proof
  apply StatMech.Walls.gc48_defect_LHSdoubled_card

/--
[gc48_defect_RHSdoubled_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean)
-/
@[path]
private lemma gc48_defect_RHSdoubled_card_eq :
-- imply
  #(gc48_RHSdoubled gc46_defectEnds (0 : Fin 4) 1 2 3) = 7 := by
-- proof
  apply StatMech.Walls.gc48_defect_RHSdoubled_card

/--
[gc48_defect_doubled_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean)
-/
@[path]
private lemma gc48_defect_doubled_le_eq :
-- imply
  #(gc48_LHSdoubled gc46_defectEnds (0 : Fin 4) 1 2 3) ≤ #(gc48_RHSdoubled gc46_defectEnds (0 : Fin 4) 1 2 3) := by
-- proof
  apply StatMech.Walls.gc48_defect_doubled_le

/--
[gc48_defect_summary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc48pairinject.lean)
-/
@[path]
private lemma gc48_defect_summary_eq :
-- imply
  gc47_PairInjection gc46_defectEnds (0 : Fin 4) 1 2 3 ∧ #(gc48_LHSdoubled gc46_defectEnds (0 : Fin 4) 1 2 3) ≤ #(gc48_RHSdoubled gc46_defectEnds (0 : Fin 4) 1 2 3) := by
-- proof
  apply StatMech.Walls.gc48_defect_summary


-- created on 2026-10-23
