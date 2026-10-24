import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.SwitchingDichotomy
open Finset BigOperators Classical StatMech StatMech.Sharpness StatMech.Sharpness.RandomCurrent


/--
[mem_compOddVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean)
-/
@[path]
private lemma mem_compOddVertices_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {u x : V} :
-- imply
  x ∈ compOddVertices ends m u ↔ connK ends m u x ∧ Odd (degK ends m x) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.mem_compOddVertices

/--
[even_compOddVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean)
-/
@[path]
private lemma even_compOddVertices_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {u : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) :
-- imply
  Even (compOddVertices ends m u).card := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.even_compOddVertices ends m hnd u

/--
[compOddVertices_eq_filter_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean)
-/
@[path]
private lemma compOddVertices_eq_filter_sources_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {u : V} :
-- imply
  compOddVertices ends m u = (sources ends m).filter (fun x => connK ends m u x) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.compOddVertices_eq_filter_sources ends m u

/--
[compOddVertices_mem_of_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean)
-/
@[path]
private lemma compOddVertices_mem_of_source_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o w : V}
-- given
  (hw : w ∈ sources ends m)
  (hconn : connK ends m o w) :
-- imply
  w ∈ compOddVertices ends m o := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.compOddVertices_mem_of_source ends m hw hconn

/--
[compOddVertices_o_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean)
-/
@[path]
private lemma compOddVertices_o_eq_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hsrc : sources ends m = {o, x, y, g})
  (hng : ¬ connK ends m o g) :
-- imply
  compOddVertices ends m o = {o, x} ∨ compOddVertices ends m o = {o, y} := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.compOddVertices_o_eq ends m hnd hox hoy hog hxy hxg hyg hsrc hng

/--
[connK_of_compOddVertices_eq_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean)
-/
@[path]
private lemma connK_of_compOddVertices_eq_pair_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o w z : V}
-- given
  (heq : compOddVertices ends m o = {o, w})
  (hzsrc : z ∈ sources ends m)
  (hzne_o : z ≠ o)
  (hzne_w : z ≠ w) :
-- imply
  connK ends m o w ∧ ¬ connK ends m o z := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.connK_of_compOddVertices_eq_pair ends m heq hzsrc hzne_o hzne_w

/--
[disconnect_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean)
-/
@[path]
private lemma disconnect_dichotomy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hsrc : sources ends m = {o, x, y, g})
  (hng : ¬ connK ends m o g) :
-- imply
  (connK ends m o x ∧ connK ends m y g) ∨ (connK ends m o y ∧ connK ends m x g) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.disconnect_dichotomy ends m hnd hox hoy hog hxy hxg hyg hsrc hng

/--
[disconnect_dichotomy_prop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean)
-/
@[path]
private lemma disconnect_dichotomy_prop_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hsrc : sources ends m = {o, x, y, g})
  (hng : ¬ connK ends m o g) :
-- imply
  (connK ends m o x ∧ connK ends m y g) ↔ ¬ (connK ends m o y ∧ connK ends m x g) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.disconnect_dichotomy_prop ends m hnd hox hoy hog hxy hxg hyg hsrc hng

/--
[connK_yg_of_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean)
-/
@[path]
private lemma connK_yg_of_disconnected_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hsrc : sources ends m = {o, x, y, g})
  (hny : ¬ connK ends m o y)
  (hng : ¬ connK ends m o g) :
-- imply
  connK ends m y g := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.connK_yg_of_disconnected ends m hnd hox hoy hog hxy hxg hyg hsrc hny hng

/--
[witEnds_not_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean)
-/
@[path]
private lemma witEnds_not_diag_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  ∀ i ∈ witM, ¬ (witEnds i).IsDiag := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.witEnds_not_diag

/--
[witM_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean)
-/
@[path]
private lemma witM_sources_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  sources witEnds witM = {0, 1, 2, 3} := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.witM_sources

/--
[witM_connK_ox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean)
-/
@[path]
private lemma witM_connK_ox_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  connK witEnds witM 0 1 := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.witM_connK_ox

/--
[witM_connK_yg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean)
-/
@[path]
private lemma witM_connK_yg_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  connK witEnds witM 2 3 := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.witM_connK_yg

/--
[witM_not_connK_og](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean)
-/
@[path]
private lemma witM_not_connK_og_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  ¬ connK witEnds witM 0 3 := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.witM_not_connK_og

/--
[disconnect_dichotomy_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean)
-/
@[path]
private lemma disconnect_dichotomy_nonvacuous_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  sources witEnds witM = ({(0 : Fin 4), 1, 2, 3} : Finset (Fin 4)) ∧ ¬ connK witEnds witM 0 3 ∧ ((connK witEnds witM 0 1 ∧ connK witEnds witM 2 3) ∨ (connK witEnds witM 0 2 ∧ connK witEnds witM 1 3)) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.disconnect_dichotomy_nonvacuous


-- created on 2026-10-23
