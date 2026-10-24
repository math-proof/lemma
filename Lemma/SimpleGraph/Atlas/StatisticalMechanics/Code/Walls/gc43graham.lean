import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc43graham
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc43_compl_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_compl_sources_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι} :
-- imply
  sources ends (univ \ M) = sources ends univ ∆ sources ends M := by
-- proof
  apply StatMech.Walls.gc43_compl_sources ends M

/--
[gc43_sd_oxyg_ox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_sd_oxyg_ox_eq
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
  ({o, x, y, g} : Finset W) ∆ ({o, x} : Finset W) = ({y, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc43_sd_oxyg_ox hox hoy hog hxy hxg hyg

/--
[gc43_compl_sources_yg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_compl_sources_yg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι}
  {o x y g : W}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (hM : sources ends M = ({o, x} : Finset W)) :
-- imply
  sources ends (univ \ M) = ({y, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc43_compl_sources_yg ends M hox hoy hog hxy hxg hyg huniv hM

/--
[gc43_compl_connK_yg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_compl_connK_yg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι}
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
  (hM : sources ends M = ({o, x} : Finset W)) :
-- imply
  connK ends (univ \ M) y g := by
-- proof
  apply StatMech.Walls.gc43_compl_connK_yg ends hnd M hox hoy hog hxy hxg hyg huniv hM

/--
[gc43_exists_reloc_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_exists_reloc_set_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι}
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
  (hM : sources ends M = ({o, x} : Finset W)) :
-- imply
  ∃ Q ⊆ univ \ M, sources ends Q = ({y, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc43_exists_reloc_set ends hnd M hox hoy hog hxy hxg hyg huniv hM

/--
[gc43_connK_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_connK_mono_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K K' : Finset ι}
  {u v : W}
-- given
  (hsub : K ⊆ K')
  (h : connK ends K u v) :
-- imply
  connK ends K' u v := by
-- proof
  apply StatMech.Walls.gc43_connK_mono ends hsub h

/--
[gc43_ox_conn_of_LHS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_ox_conn_of_LHS_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M : Finset ι}
  {o x : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hM : sources ends M = ({o, x} : Finset W)) :
-- imply
  connK ends M o x := by
-- proof
  apply StatMech.Walls.gc43_ox_conn_of_LHS ends hnd M hox hM

/--
[gc43_yg_conn_of_Q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_yg_conn_of_Q_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {Q : Finset ι}
  {y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hyg : y ≠ g)
  (hQ : sources ends Q = ({y, g} : Finset W)) :
-- imply
  connK ends Q y g := by
-- proof
  apply StatMech.Walls.gc43_yg_conn_of_Q ends hnd Q hyg hQ

/--
[gc43_reloc_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_reloc_sources_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M Q : Finset ι}
  {o x y g : W}
-- given
  (hQsub : Q ⊆ univ \ M)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hM : sources ends M = ({o, x} : Finset W))
  (hQ : sources ends Q = ({y, g} : Finset W)) :
-- imply
  sources ends (M ∪ Q) = ({o, x, y, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc43_reloc_sources ends hQsub hox hoy hog hxy hxg hyg hM hQ

/--
[gc43_reloc_in_RHS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_reloc_in_RHS_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M Q : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hQsub : Q ⊆ univ \ M)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hM : sources ends M = ({o, x} : Finset W))
  (hQ : sources ends Q = ({y, g} : Finset W))
  (hxg_conn : connK ends M x g) :
-- imply
  sources ends (M ∪ Q) = ({o, x, y, g} : Finset W) ∧ connK ends (M ∪ Q) o x ∧ connK ends (M ∪ Q) o y ∧ connK ends (M ∪ Q) o g := by
-- proof
  apply StatMech.Walls.gc43_reloc_in_RHS ends hnd hQsub hox hoy hog hxy hxg hyg hM hQ hxg_conn

/--
[gc43_E_le_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_E_le_of_subset_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M N : Finset ι}
-- given
  (hMN : M ⊆ N) :
-- imply
  gc40_E ends M ≤ gc40_E ends N := by
-- proof
  apply StatMech.Walls.gc43_E_le_of_subset ends hMN

/--
[gc43_reloc_E_dom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_reloc_E_dom_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {M Q : Finset ι} :
-- imply
  gc40_E ends M ≤ gc40_E ends (M ∪ Q) := by
-- proof
  apply StatMech.Walls.gc43_reloc_E_dom ends M Q

/--
[gc43_LHS_eq_gatedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_LHS_eq_gatedSum_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W} :
-- imply
  (∑ M ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x} : Finset W)), (if connK ends M x g then gc40_E ends M else 0)) = ∑ M ∈ gc43_Lset ends o x y g, gc40_E ends M := by
-- proof
  apply StatMech.Walls.gc43_LHS_eq_gatedSum ends o x y g

/--
[gc43_RHS_eq_gatedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_RHS_eq_gatedSum_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W} :
-- imply
  (∑ M ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x, y, g} : Finset W)), (if connK ends M o x ∧ connK ends M o y ∧ connK ends M o g then gc40_E ends M else 0)) = ∑ M ∈ gc43_Rset ends o x y g, gc40_E ends M := by
-- proof
  apply StatMech.Walls.gc43_RHS_eq_gatedSum ends o x y g

/--
[gc43_EMass_of_fibreDomReloc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_EMass_of_fibreDomReloc_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (h : gc43_FibreDomReloc ends o x y g) :
-- imply
  gc42_EMassResidue ends o x y g := by
-- proof
  apply StatMech.Walls.gc43_EMass_of_fibreDomReloc ends o x y g h

/--
[gc43_countIneq_of_fibreDomReloc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_countIneq_of_fibreDomReloc_eq
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
  (h : gc43_FibreDomReloc ends o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc43_countIneq_of_fibreDomReloc ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc43_per_M_reloc_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_per_M_reloc_exists_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
  {M : Finset ι}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (hM : M ∈ gc43_Lset ends o x y g) :
-- imply
  ∃ M' ∈ gc43_Rset ends o x y g, M ⊆ M' ∧ gc40_E ends M ≤ gc40_E ends M' := by
-- proof
  apply StatMech.Walls.gc43_per_M_reloc_exists ends hnd hox hoy hog hxy hxg hyg huniv hM

/--
[gc43_claw_Lset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_claw_Lset_eq :
-- imply
  gc43_Lset gc40_clawEnds (0 : Fin 4) 1 2 3 = {({0, 1} : Finset (Fin 3))} := by
-- proof
  apply StatMech.Walls.gc43_claw_Lset

/--
[gc43_claw_Rset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_claw_Rset_eq :
-- imply
  gc43_Rset gc40_clawEnds (0 : Fin 4) 1 2 3 = {({0, 1, 2} : Finset (Fin 3))} := by
-- proof
  apply StatMech.Walls.gc43_claw_Rset

/--
[gc43_claw_FibreDomReloc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_claw_FibreDomReloc_eq :
-- imply
  gc43_FibreDomReloc gc40_clawEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc43_claw_FibreDomReloc

/--
[gc43_claw_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_claw_core_eq :
-- imply
  gc39_ThreeColouringCountIneq gc40_clawEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc43_claw_core

/--
[gc43_reloc_applies_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean)
-/
@[path]
private lemma gc43_reloc_applies_claw_eq :
-- imply
  (∀ i : Fin 3, ¬ (gc40_clawEnds i).IsDiag) ∧ ((0 : Fin 4) ≠ 1 ∧ (0 : Fin 4) ≠ 2 ∧ (0 : Fin 4) ≠ 3 ∧ (1 : Fin 4) ≠ 2 ∧ (1 : Fin 4) ≠ 3 ∧ (2 : Fin 4) ≠ 3) ∧ sources gc40_clawEnds (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4)) ∧ gc43_FibreDomReloc gc40_clawEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc43_reloc_applies_claw


-- created on 2026-10-23
