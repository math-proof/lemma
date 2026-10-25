import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc45cycle.Part4
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc45_E_eq_card_evenSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_E_eq_card_evenSub_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι} :
-- imply
  gc40_E ends M = #(gc45_evenSub ends M) := by
-- proof
  apply StatMech.Walls.gc45_E_eq_card_evenSub ends M

/--
[gc45_empty_mem_evenSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_empty_mem_evenSub_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι} :
-- imply
  (∅ : Finset ι) ∈ gc45_evenSub ends M := by
-- proof
  apply StatMech.Walls.gc45_empty_mem_evenSub ends M

/--
[gc45_evenSub_symmDiff_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_evenSub_symmDiff_mem_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι}
  {S T : Finset ι}
-- given
  (hS : S ∈ gc45_evenSub ends M)
  (hT : T ∈ gc45_evenSub ends M) :
-- imply
  S ∆ T ∈ gc45_evenSub ends M := by
-- proof
  apply StatMech.Walls.gc45_evenSub_symmDiff_mem ends M hS hT

/--
[gc45_E_eq_one_of_evenSub_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_E_eq_one_of_evenSub_singleton_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι}
-- given
  (h : gc45_evenSub ends M = {(∅ : Finset ι)}) :
-- imply
  gc40_E ends M = 1 := by
-- proof
  apply StatMech.Walls.gc45_E_eq_one_of_evenSub_singleton ends M h

/--
[gc45_E_eq_two_of_nullity_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_E_eq_two_of_nullity_one_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι}
  {C : Finset ι}
-- given
  (hCne : C ≠ (∅ : Finset ι))
  (h : gc45_evenSub ends M = {(∅ : Finset ι), C}) :
-- imply
  gc40_E ends M = 2 := by
-- proof
  apply StatMech.Walls.gc45_E_eq_two_of_nullity_one ends M hCne h

/--
[gc45_fibreDomReloc_of_injOn_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_fibreDomReloc_of_injOn_subset_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
  {φ : Finset ι → Finset ι}
-- given
  (hmaps : ∀ M ∈ gc43_Lset ends o x y g, φ M ∈ gc43_Rset ends o x y g)
  (hsub : ∀ M ∈ gc43_Lset ends o x y g, M ⊆ φ M)
  (hinj : Set.InjOn φ (gc43_Lset ends o x y g)) :
-- imply
  gc43_FibreDomReloc ends o x y g := by
-- proof
  apply StatMech.Walls.gc45_fibreDomReloc_of_injOn_subset ends o x y g φ hmaps hsub hinj

/--
[gc45_FibreDomReloc_of_disjointBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_FibreDomReloc_of_disjointBridge_eq
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
  (hbridge : gc44_DisjointBridge ends o x y g) :
-- imply
  gc43_FibreDomReloc ends o x y g := by
-- proof
  apply StatMech.Walls.gc45_FibreDomReloc_of_disjointBridge ends hnd hox hoy hog hxy hxg hyg hbridge

/--
[gc45_fibreDomReloc_of_count_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_fibreDomReloc_of_count_le_eq
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
  (hcount : ∀ M' ∈ gc43_Rset ends o x y g, #((gc43_Lset ends o x y g).filter (fun M => φ M = M')) ≤ gc40_E ends M') :
-- imply
  gc43_FibreDomReloc ends o x y g := by
-- proof
  apply StatMech.Walls.gc45_fibreDomReloc_of_count_le ends o x y g htree φ hmaps hcount

/--
[gc45_FibreDomReloc_of_nullityOneReloc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_FibreDomReloc_of_nullityOneReloc_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (htree : gc45_TreeLHS ends o x y g)
  (hreloc : gc45_NullityOneRelocation ends o x y g) :
-- imply
  gc43_FibreDomReloc ends o x y g := by
-- proof
  apply StatMech.Walls.gc45_FibreDomReloc_of_nullityOneReloc ends o x y g htree hreloc

/--
[gc45_EMassResidue_of_nullityOneReloc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_EMassResidue_of_nullityOneReloc_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (htree : gc45_TreeLHS ends o x y g)
  (hreloc : gc45_NullityOneRelocation ends o x y g) :
-- imply
  gc42_EMassResidue ends o x y g := by
-- proof
  apply StatMech.Walls.gc45_EMassResidue_of_nullityOneReloc ends o x y g htree hreloc

/--
[gc45_countIneq_of_nullityOneReloc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_countIneq_of_nullityOneReloc_eq
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
  (htree : gc45_TreeLHS ends o x y g)
  (hreloc : gc45_NullityOneRelocation ends o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc45_countIneq_of_nullityOneReloc ends hnd hox hoy hog hxy hxg hyg huniv htree hreloc

/--
[gc45_diamondEnds_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_diamondEnds_loopless_eq :
-- imply
  ∀ i : Fin 4, ¬ (gc45_diamondEnds i).IsDiag := by
-- proof
  apply StatMech.Walls.gc45_diamondEnds_loopless

/--
[gc45_diamondEnds_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_diamondEnds_univ_sources_eq :
-- imply
  sources gc45_diamondEnds (univ : Finset (Fin 4)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc45_diamondEnds_univ_sources

/--
[gc45_diamond_evenSub_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_diamond_evenSub_univ_eq :
-- imply
  gc45_evenSub gc45_diamondEnds (univ : Finset (Fin 4)) = {(∅ : Finset (Fin 4)), ({0, 3} : Finset (Fin 4))} := by
-- proof
  apply StatMech.Walls.gc45_diamond_evenSub_univ

/--
[gc45_diamond_E_univ_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_diamond_E_univ_eq_two_eq :
-- imply
  gc40_E gc45_diamondEnds (univ : Finset (Fin 4)) = 2 := by
-- proof
  apply StatMech.Walls.gc45_diamond_E_univ_eq_two

/--
[gc45_diamond_not_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_diamond_not_forest_eq :
-- imply
  ¬ gc44_ForestHyp gc45_diamondEnds := by
-- proof
  apply StatMech.Walls.gc45_diamond_not_forest

/--
[gc45_diamond_Lset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_diamond_Lset_eq :
-- imply
  gc43_Lset gc45_diamondEnds (0 : Fin 4) 1 2 3 = {({0, 1} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4))} := by
-- proof
  apply StatMech.Walls.gc45_diamond_Lset

/--
[gc45_diamond_reach_12_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_diamond_reach_12_subset_eq
  {v : Fin 4}
-- given
  (h : connK gc45_diamondEnds ({1, 2} : Finset (Fin 4)) (0 : Fin 4) v) :
-- imply
  v ∈ ({0, 2} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc45_diamond_reach_12_subset h

/--
[gc45_diamond_not_conn_12_01](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_diamond_not_conn_12_01_eq :
-- imply
  ¬ connK gc45_diamondEnds ({1, 2} : Finset (Fin 4)) (0 : Fin 4) (1 : Fin 4) := by
-- proof
  apply StatMech.Walls.gc45_diamond_not_conn_12_01

/--
[gc45_diamond_Rset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_diamond_Rset_eq :
-- imply
  gc43_Rset gc45_diamondEnds (0 : Fin 4) 1 2 3 = {(univ : Finset (Fin 4))} := by
-- proof
  apply StatMech.Walls.gc45_diamond_Rset

/--
[gc45_diamond_TreeLHS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_diamond_TreeLHS_eq :
-- imply
  gc45_TreeLHS gc45_diamondEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc45_diamond_TreeLHS

/--
[gc45_diamond_NullityOneRelocation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_diamond_NullityOneRelocation_eq :
-- imply
  gc45_NullityOneRelocation gc45_diamondEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc45_diamond_NullityOneRelocation

/--
[gc45_diamond_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_diamond_core_eq :
-- imply
  gc39_ThreeColouringCountIneq gc45_diamondEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc45_diamond_core

/--
[gc45_diamond_EMassResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_diamond_EMassResidue_eq :
-- imply
  gc42_EMassResidue gc45_diamondEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc45_diamond_EMassResidue

/--
[gc45_reloc_applies_diamond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean)
-/
@[path]
private lemma gc45_reloc_applies_diamond_eq :
-- imply
  (∀ i : Fin 4, ¬ (gc45_diamondEnds i).IsDiag) ∧ sources gc45_diamondEnds (univ : Finset (Fin 4)) = ({0, 1, 2, 3} : Finset (Fin 4)) ∧ gc40_E gc45_diamondEnds (univ : Finset (Fin 4)) = 2 ∧ gc45_TreeLHS gc45_diamondEnds (0 : Fin 4) 1 2 3 ∧ gc45_NullityOneRelocation gc45_diamondEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc45_reloc_applies_diamond


-- created on 2026-10-23
