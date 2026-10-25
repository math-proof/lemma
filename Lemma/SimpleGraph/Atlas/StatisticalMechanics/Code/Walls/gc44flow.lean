import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc44flow.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc44_fibreDomReloc_of_injOn_of_E_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc44flow.lean)
-/
@[path]
private lemma gc44_fibreDomReloc_of_injOn_of_E_one_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
  {φ : Finset ι → Finset ι}
-- given
  (hE : gc44_ForestHyp ends)
  (hmaps : ∀ M ∈ gc43_Lset ends o x y g, φ M ∈ gc43_Rset ends o x y g)
  (hinj : Set.InjOn φ (gc43_Lset ends o x y g)) :
-- imply
  gc43_FibreDomReloc ends o x y g := by
-- proof
  apply StatMech.Walls.gc44_fibreDomReloc_of_injOn_of_E_one ends o x y g hE φ hmaps hinj

/--
[gc44_sd_ox_yg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc44flow.lean)
-/
@[path]
private lemma gc44_sd_ox_yg_eq
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
  ({o, x} : Finset W) ∆ ({y, g} : Finset W) = ({o, x, y, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc44_sd_ox_yg hox hoy hog hxy hxg hyg

/--
[gc44_shift_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc44flow.lean)
-/
@[path]
private lemma gc44_shift_sources_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M P : Finset ι}
  {o x y g : W}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hM : sources ends M = ({o, x} : Finset W))
  (hP : sources ends P = ({y, g} : Finset W)) :
-- imply
  sources ends (M ∆ P) = ({o, x, y, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc44_shift_sources ends hox hoy hog hxy hxg hyg hM hP

/--
[gc44_shift_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc44flow.lean)
-/
@[path]
private lemma gc44_shift_injOn_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {P : Finset ι}
  {s : Finset (Finset ι)} :
-- imply
  Set.InjOn (fun M => M ∆ P) s := by
-- proof
  apply StatMech.Walls.gc44_shift_injOn ends P s

/--
[gc44_shift_in_Rset_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc44flow.lean)
-/
@[path]
private lemma gc44_shift_in_Rset_of_disjoint_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M P : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hdisj : Disjoint M P)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hM : sources ends M = ({o, x} : Finset W))
  (hP : sources ends P = ({y, g} : Finset W))
  (hxg_conn : connK ends M x g) :
-- imply
  M ∆ P ∈ gc43_Rset ends o x y g := by
-- proof
  apply StatMech.Walls.gc44_shift_in_Rset_of_disjoint ends hnd hdisj hox hoy hog hxy hxg hyg hM hP hxg_conn

/--
[gc44_FibreDomReloc_of_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc44flow.lean)
-/
@[path]
private lemma gc44_FibreDomReloc_of_forest_eq
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
  (hforest : gc44_ForestHyp ends)
  (hbridge : gc44_DisjointBridge ends o x y g) :
-- imply
  gc43_FibreDomReloc ends o x y g := by
-- proof
  apply StatMech.Walls.gc44_FibreDomReloc_of_forest ends hnd hox hoy hog hxy hxg hyg hforest hbridge

/--
[gc44_countIneq_of_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc44flow.lean)
-/
@[path]
private lemma gc44_countIneq_of_forest_eq
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
  (hforest : gc44_ForestHyp ends)
  (hbridge : gc44_DisjointBridge ends o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc44_countIneq_of_forest ends hnd hox hoy hog hxy hxg hyg huniv hforest hbridge

/--
[gc44_EMassResidue_of_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc44flow.lean)
-/
@[path]
private lemma gc44_EMassResidue_of_forest_eq
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
  (hforest : gc44_ForestHyp ends)
  (hbridge : gc44_DisjointBridge ends o x y g) :
-- imply
  gc42_EMassResidue ends o x y g := by
-- proof
  apply StatMech.Walls.gc44_EMassResidue_of_forest ends hnd hox hoy hog hxy hxg hyg hforest hbridge

/--
[gc44_claw_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc44flow.lean)
-/
@[path]
private lemma gc44_claw_forest_eq :
-- imply
  gc44_ForestHyp gc40_clawEnds := by
-- proof
  apply StatMech.Walls.gc44_claw_forest

/--
[gc44_claw_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc44flow.lean)
-/
@[path]
private lemma gc44_claw_bridge_eq :
-- imply
  gc44_DisjointBridge gc40_clawEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc44_claw_bridge

/--
[gc44_claw_FibreDomReloc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc44flow.lean)
-/
@[path]
private lemma gc44_claw_FibreDomReloc_eq :
-- imply
  gc43_FibreDomReloc gc40_clawEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc44_claw_FibreDomReloc

/--
[gc44_claw_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc44flow.lean)
-/
@[path]
private lemma gc44_claw_core_eq :
-- imply
  gc39_ThreeColouringCountIneq gc40_clawEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc44_claw_core

/--
[gc44_reloc_applies_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc44flow.lean)
-/
@[path]
private lemma gc44_reloc_applies_claw_eq :
-- imply
  (∀ i : Fin 3, ¬ (gc40_clawEnds i).IsDiag) ∧ ((0 : Fin 4) ≠ 1 ∧ (0 : Fin 4) ≠ 2 ∧ (0 : Fin 4) ≠ 3 ∧ (1 : Fin 4) ≠ 2 ∧ (1 : Fin 4) ≠ 3 ∧ (2 : Fin 4) ≠ 3) ∧ sources gc40_clawEnds (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4)) ∧ gc44_ForestHyp gc40_clawEnds ∧ gc44_DisjointBridge gc40_clawEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc44_reloc_applies_claw


-- created on 2026-10-23
