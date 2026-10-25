import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc67removable
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc67b_degK_symmDiff_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc67removable.lean)
-/
@[path]
private lemma gc67b_degK_symmDiff_notMem_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {Q : Finset ι}
  {i : ι}
  {g : W}
-- given
  (hi : g ∉ ends i) :
-- imply
  degK ends (Q ∆ ({i} : Finset ι)) g = degK ends Q g := by
-- proof
  apply StatMech.Walls.gc67b_degK_symmDiff_notMem ends Q hi

/--
[gc67b_gdeg1_connector_of_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc67removable.lean)
-/
@[path]
private lemma gc67b_gdeg1_connector_of_conn_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {D : Finset ι}
  {y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hyg : y ≠ g)
  (hconn : connK ends D y g) :
-- imply
  ∃ P, P ⊆ D ∧ sources ends P = ({y, g} : Finset W) ∧ degK ends P g = 1 := by
-- proof
  apply StatMech.Walls.gc67b_gdeg1_connector_of_conn ends hnd hyg hconn

/--
[gc67b_removableGEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc67removable.lean)
-/
@[path]
private lemma gc67b_removableGEdge_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hyg : y ≠ g) :
-- imply
  gc66_RemovableGEdge ends K y g := by
-- proof
  apply StatMech.Walls.gc67b_removableGEdge ends hnd K hyg

/--
[gc67b_choose_D](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc67removable.lean)
-/
@[path]
private lemma gc67b_choose_D_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (hKsrc : sources ends K = ({o, x} : Finset W)) :
-- imply
  ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ degK ends D g = 1 := by
-- proof
  apply StatMech.Walls.gc67b_choose_D ends hnd K hoy hog hxy hxg hyg huniv hKsrc

/--
[gc67b_witness_removableGEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc67removable.lean)
-/
@[path]
private lemma gc67b_witness_removableGEdge_eq :
-- imply
  gc66_RemovableGEdge gc59_witnessEnds ({0} : Finset (Fin 5)) 2 3 := by
-- proof
  apply StatMech.Walls.gc67b_witness_removableGEdge

/--
[gc67b_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc67removable.lean)
-/
@[path]
private lemma gc67b_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (y g : W), y ≠ g → gc66_RemovableGEdge ends K y g) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W), o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g → sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) → sources ends K = ({o, x} : Finset W) → ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ degK ends D g = 1) ∧ gc66_RemovableGEdge gc59_witnessEnds ({0} : Finset (Fin 5)) 2 3 := by
-- proof
  apply StatMech.Walls.gc67b_status


-- created on 2026-10-23
