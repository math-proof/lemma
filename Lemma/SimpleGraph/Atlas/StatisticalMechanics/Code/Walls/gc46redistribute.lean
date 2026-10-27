import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc46redistribute.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc46_card_symmDiff_closed_eq_two_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc46redistribute.lean)
-/
@[path]
private lemma gc46_card_symmDiff_closed_eq_two_pow_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {F : Finset (Finset ι)}
-- given
  (h0 : (∅ : Finset ι) ∈ F)
  (hclosed : ∀ a ∈ F, ∀ b ∈ F, a ∆ b ∈ F) :
-- imply
  ∃ n : ℕ, #F = 2 ^ n := by
-- proof
  apply StatMech.Walls.gc46_card_symmDiff_closed_eq_two_pow F h0 hclosed

/--
[gc46_E_eq_two_pow_nullity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc46redistribute.lean)
-/
@[path]
private lemma gc46_E_eq_two_pow_nullity_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι} :
-- imply
  ∃ n : ℕ, gc40_E ends M = 2 ^ n := by
-- proof
  apply StatMech.Walls.gc46_E_eq_two_pow_nullity ends M

/--
[gc46_E_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc46redistribute.lean)
-/
@[path]
private lemma gc46_E_pos_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι} :
-- imply
  1 ≤ gc40_E ends M := by
-- proof
  apply StatMech.Walls.gc46_E_pos ends M

/--
[gc46_E_eq_two_pow_log](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc46redistribute.lean)
-/
@[path]
private lemma gc46_E_eq_two_pow_log_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι} :
-- imply
  gc40_E ends M = 2 ^ (Nat.log 2 (gc40_E ends M)) := by
-- proof
  apply StatMech.Walls.gc46_E_eq_two_pow_log ends M

/--
[gc46_sameBoundary_subfamily_card_le_E](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc46redistribute.lean)
-/
@[path]
private lemma gc46_sameBoundary_subfamily_card_le_E_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M' : Finset ι}
  {b : Finset W}
  {𝓕 : Finset (Finset ι)}
-- given
  (hsub : ∀ M ∈ 𝓕, M ⊆ M')
  (hbd : ∀ M ∈ 𝓕, sources ends M = b) :
-- imply
  #𝓕 ≤ gc40_E ends M' := by
-- proof
  apply StatMech.Walls.gc46_sameBoundary_subfamily_card_le_E ends M' b 𝓕 hsub hbd

/--
[gc46_fibre_card_le_E](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc46redistribute.lean)
-/
@[path]
private lemma gc46_fibre_card_le_E_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
  {φ : Finset ι → Finset ι}
  {M' : Finset ι}
-- given
  (hsub : ∀ M ∈ gc43_Lset ends o x y g, M ⊆ φ M)
  (hM' : M' ∈ gc43_Rset ends o x y g) :
-- imply
  #((gc43_Lset ends o x y g).filter (fun M => φ M = M')) ≤ gc40_E ends M' := by
-- proof
  apply StatMech.Walls.gc46_fibre_card_le_E ends o x y g φ hsub hM'

/--
[gc46_fibreDomReloc_of_treeLHS_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc46redistribute.lean)
-/
@[path]
private lemma gc46_fibreDomReloc_of_treeLHS_subset_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
  {φ : Finset ι → Finset ι}
-- given
  (htree : gc45_TreeLHS ends o x y g)
  (hmaps : ∀ M ∈ gc43_Lset ends o x y g, φ M ∈ gc43_Rset ends o x y g)
  (hsub : ∀ M ∈ gc43_Lset ends o x y g, M ⊆ φ M) :
-- imply
  gc43_FibreDomReloc ends o x y g := by
-- proof
  apply StatMech.Walls.gc46_fibreDomReloc_of_treeLHS_subset ends o x y g htree φ hmaps hsub

/--
[gc46_defectEnds_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc46redistribute.lean)
-/
@[path]
private lemma gc46_defectEnds_loopless_eq :
-- imply
  ∀ i : Fin 5, ¬ (gc46_defectEnds i).IsDiag := by
-- proof
  apply StatMech.Walls.gc46_defectEnds_loopless

/--
[gc46_defectEnds_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc46redistribute.lean)
-/
@[path]
private lemma gc46_defectEnds_univ_sources_eq :
-- imply
  sources gc46_defectEnds (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc46_defectEnds_univ_sources

/--
[gc46_defect_Lset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc46redistribute.lean)
-/
@[path]
private lemma gc46_defect_Lset_eq :
-- imply
  gc43_Lset gc46_defectEnds (0 : Fin 4) 1 2 3 = {({3, 4} : Finset (Fin 5)), {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}} := by
-- proof
  apply StatMech.Walls.gc46_defect_Lset

/--
[gc46_defect_Rset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc46redistribute.lean)
-/
@[path]
private lemma gc46_defect_Rset_eq :
-- imply
  gc43_Rset gc46_defectEnds (0 : Fin 4) 1 2 3 = {({0, 3, 4} : Finset (Fin 5)), {1, 3, 4}, {2, 3, 4}, univ} := by
-- proof
  apply StatMech.Walls.gc46_defect_Rset

/--
[gc46_defect_EMassResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc46redistribute.lean)
-/
@[path]
private lemma gc46_defect_EMassResidue_eq :
-- imply
  gc42_EMassResidue gc46_defectEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc46_defect_EMassResidue

/--
[gc46_defect_not_FibreDomReloc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc46redistribute.lean)
-/
@[path]
private lemma gc46_defect_not_FibreDomReloc_eq :
-- imply
  ¬ gc43_FibreDomReloc gc46_defectEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc46_defect_not_FibreDomReloc

/--
[gc46_fibreDomReloc_strictly_stronger](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc46redistribute.lean)
-/
@[path]
private lemma gc46_fibreDomReloc_strictly_stronger_eq :
-- imply
  gc42_EMassResidue gc46_defectEnds (0 : Fin 4) 1 2 3 ∧ ¬ gc43_FibreDomReloc gc46_defectEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc46_fibreDomReloc_strictly_stronger


-- created on 2026-10-23
