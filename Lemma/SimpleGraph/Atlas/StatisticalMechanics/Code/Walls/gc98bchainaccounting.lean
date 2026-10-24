import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc98bchainaccounting
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc98b_accounting_iff_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc98bchainaccounting.lean)
-/
@[path]
private lemma gc98b_accounting_iff_target_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  gc98b_DisjointAccounting ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g := by
-- proof
  apply StatMech.Walls.gc98b_accounting_iff_target ends m o x y g

/--
[gc98b_disjoint_accounting_closes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc98bchainaccounting.lean)
-/
@[path]
private lemma gc98b_disjoint_accounting_closes_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hda : gc98b_DisjointAccounting ends m o x y g) :
-- imply
  gc85b_ThreeCurrentBijection ends m o x y g := by
-- proof
  apply StatMech.Walls.gc98b_disjoint_accounting_closes ends m o x y g hda

/--
[gc98b_chain_of_cogxg_le_T3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc98bchainaccounting.lean)
-/
@[path]
private lemma gc98b_chain_of_cogxg_le_T3_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hsrc : sources ends m = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hle : gc87b_CogxgLeT3 ends m o x y g) :
-- imply
  gc85b_ThreeCurrentBijection ends m o x y g := by
-- proof
  apply StatMech.Walls.gc98b_chain_of_cogxg_le_T3 ends m hnd hsrc hox hoy hog hle

/--
[gc98b_tri_image_too_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc98bchainaccounting.lean)
-/
@[path]
private lemma gc98b_tri_image_too_small_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  #(gc98b_cogRerouteImage gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3) = 1 ∧ 2 * gc85b_pcount gc87b_triEnds (univ : Finset (Fin 3)) {0, 3} {1, 3} = 2 ∧ #(gc98b_cogRerouteImage gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3) < 2 * gc85b_pcount gc87b_triEnds (univ : Finset (Fin 3)) {0, 3} {1, 3} := by
-- proof
  apply StatMech.Walls.gc98b_tri_image_too_small

/--
[gc98b_cogRerouteImage_subset_RHS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc98bchainaccounting.lean)
-/
@[path]
private lemma gc98b_cogRerouteImage_subset_RHS_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  ∀ LL ∈ gc98b_cogRerouteImage ends m o x y g, Disjoint LL.1 LL.2 ∧ sources ends LL.1 = (∅ : Finset W) ∧ (sources ends LL.2 = ({o, g} : Finset W) ∨ sources ends LL.2 = ({o, x} : Finset W) ∨ sources ends LL.2 = ({o, y} : Finset W)) := by
-- proof
  apply StatMech.Walls.gc98b_cogRerouteImage_subset_RHS ends m o x y g

/--
[gc98b_overlap_pinned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc98bchainaccounting.lean)
-/
@[path]
private lemma gc98b_overlap_pinned_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  (gc98b_DisjointAccounting ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g) ∧ (gc98b_DisjointAccounting ends m o x y g → gc85b_ThreeCurrentBijection ends m o x y g) ∧ (#(gc98b_cogRerouteImage gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3) < 2 * gc85b_pcount gc87b_triEnds (univ : Finset (Fin 3)) {0, 3} {1, 3}) := by
-- proof
  apply StatMech.Walls.gc98b_overlap_pinned ends m o x y g

/--
[gc98b_machine_findings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc98bchainaccounting.lean)
-/
@[path]
private lemma gc98b_machine_findings_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gc98b_machine_findings


-- created on 2026-10-23
