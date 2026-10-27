import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc40count.Part5
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc40_sources_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean)
-/
@[path]
private lemma gc40_sources_compl_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {S : Finset ι} :
-- imply
  sources ends (univ \ S) = sources ends univ ∆ sources ends S := by
-- proof
  apply StatMech.Walls.gc40_sources_compl ends S

/--
[gc40_sd_oxyg_og](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean)
-/
@[path]
private lemma gc40_sd_oxyg_og_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {o x y g : W}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g) :
-- imply
  ({o, x, y, g} : Finset W) ∆ ({o, g} : Finset W) = ({x, y} : Finset W) := by
-- proof
  apply StatMech.Walls.gc40_sd_oxyg_og hox hoy hog hxy hxg hyg

/--
[gc40_sd_xy_yg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean)
-/
@[path]
private lemma gc40_sd_xy_yg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {x y g : W}
-- given
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g) :
-- imply
  ({x, y} : Finset W) ∆ ({y, g} : Finset W) = ({x, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc40_sd_xy_yg hxy hxg hyg

/--
[gc40_sd_xy_xy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean)
-/
@[path]
private lemma gc40_sd_xy_xy_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {o x y g : W}
-- given
  (hxy : x ≠ y) :
-- imply
  ({x, y} : Finset W) ∆ ({x, y} : Finset W) = (∅ : Finset W) := by
-- proof
  apply StatMech.Walls.gc40_sd_xy_xy hxy

/--
[gc40_pairCount_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean)
-/
@[path]
private lemma gc40_pairCount_reindex_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [DecidablePred P]
  [∀ a, DecidablePred (Q a)]
-- given
  (P : Finset ι → Prop)
  (Q : Finset ι → Finset ι → Prop) :
-- imply
  #((univ : Finset (Finset ι × Finset ι)).filter (fun p => p.2 ⊆ univ \ p.1 ∧ P p.1 ∧ Q p.1 p.2)) = ∑ S₁ ∈ (univ : Finset ι).powerset.filter (fun S => P S), #((univ \ S₁).powerset.filter (fun S₂ => Q S₁ S₂)) := by
-- proof
  apply StatMech.Walls.gc40_pairCount_reindex P Q

/--
[gc40_inner_drop_third](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean)
-/
@[path]
private lemma gc40_inner_drop_third_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι}
  {x y g : W}
-- given
  (hMsrc : sources ends M = ({x, y} : Finset W))
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hxy : x ≠ y) :
-- imply
  M.powerset.filter (fun S₂ => sources ends S₂ = ({x, g} : Finset W) ∧ sources ends (M \ S₂) = ({y, g} : Finset W)) = M.powerset.filter (fun S₂ => sources ends S₂ = ({x, g} : Finset W)) := by
-- proof
  apply StatMech.Walls.gc40_inner_drop_third ends M hMsrc hxg hyg hxy

/--
[gc40_inner_count_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean)
-/
@[path]
private lemma gc40_inner_count_collapse_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι}
  {x y g : W}
-- given
  (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag)
  (hMsrc : sources ends M = ({x, y} : Finset W))
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hxy : x ≠ y) :
-- imply
  #(M.powerset.filter (fun S₂ => sources ends S₂ = ({x, g} : Finset W))) = (if connK ends M y g then gc40_E ends M else 0) := by
-- proof
  apply StatMech.Walls.gc40_inner_count_collapse ends M hnd hMsrc hxg hyg hxy

/--
[gc40_countIneq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean)
-/
@[path]
private lemma gc40_countIneq_iff_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W} :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g ↔ gc40_NR ends o x y g ≤ gc40_NL ends o x y g := by
-- proof
  apply StatMech.Walls.gc40_countIneq_iff ends o x y g

/--
[gc40_NR_eq_Esum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean)
-/
@[path]
private lemma gc40_NR_eq_Esum_eq
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
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
-- imply
  gc40_NR ends o x y g = ∑ S₁ ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, g} : Finset W)), (if connK ends (univ \ S₁) y g then gc40_E ends (univ \ S₁) else 0) := by
-- proof
  apply StatMech.Walls.gc40_NR_eq_Esum ends hnd hox hoy hog hxy hxg hyg huniv

/--
[gc40_NL_eq_sum_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean)
-/
@[path]
private lemma gc40_NL_eq_sum_inner_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
-- imply
  gc40_NL ends o x y g = ∑ S₁ ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x, y, g} : Finset W)), gc40_L ends S₁ o x y g := by
-- proof
  apply StatMech.Walls.gc40_NL_eq_sum_inner ends huniv

/--
[gc40_countIneq_of_EWeighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean)
-/
@[path]
private lemma gc40_countIneq_of_EWeighted_eq
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
  (hres : gc40_EWeightedCountResidue ends o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc40_countIneq_of_EWeighted ends hnd hox hoy hog hxy hxg hyg huniv hres

/--
[gc40_L_le_E](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean)
-/
@[path]
private lemma gc40_L_le_E_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {S₁ : Finset ι}
  {o x y g : W} :
-- imply
  gc40_L ends S₁ o x y g ≤ gc40_E ends (univ \ S₁) := by
-- proof
  apply StatMech.Walls.gc40_L_le_E ends S₁ o x y g

/--
[gc40_NRsummand_le_E](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean)
-/
@[path]
private lemma gc40_NRsummand_le_E_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {S₁ : Finset ι}
  {y g : W} :
-- imply
  (if connK ends (univ \ S₁) y g then gc40_E ends (univ \ S₁) else 0) ≤ gc40_E ends (univ \ S₁) := by
-- proof
  apply StatMech.Walls.gc40_NRsummand_le_E ends S₁

/--
[gc40_clawEnds_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean)
-/
@[path]
private lemma gc40_clawEnds_loopless_eq :
-- imply
  ∀ i : Fin 3, ¬ (gc40_clawEnds i).IsDiag := by
-- proof
  apply StatMech.Walls.gc40_clawEnds_loopless

/--
[gc40_clawEnds_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean)
-/
@[path]
private lemma gc40_clawEnds_univ_sources_eq :
-- imply
  sources gc40_clawEnds (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc40_clawEnds_univ_sources

/--
[gc40_reduction_applies_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean)
-/
@[path]
private lemma gc40_reduction_applies_claw_eq :
-- imply
  (∀ i : Fin 3, ¬ (gc40_clawEnds i).IsDiag) ∧ ((0 : Fin 4) ≠ 1 ∧ (0 : Fin 4) ≠ 2 ∧ (0 : Fin 4) ≠ 3 ∧ (1 : Fin 4) ≠ 2 ∧ (1 : Fin 4) ≠ 3 ∧ (2 : Fin 4) ≠ 3) ∧ sources gc40_clawEnds (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc40_reduction_applies_claw

/--
[gc40_claw_residue_closes_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean)
-/
@[path]
private lemma gc40_claw_residue_closes_core_eq
-- given
  (hres : gc40_EWeightedCountResidue gc40_clawEnds (0 : Fin 4) 1 2 3) :
-- imply
  gc39_ThreeColouringCountIneq gc40_clawEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc40_claw_residue_closes_core hres


-- created on 2026-10-23
