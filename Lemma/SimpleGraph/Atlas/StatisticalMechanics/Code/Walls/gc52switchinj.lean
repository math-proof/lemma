import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc52switchinj
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc52_selector_complete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc52switchinj.lean)
-/
@[path]
private lemma gc52_selector_complete_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
  {L Q : Finset ι}
-- given
  (hL : L ∈ gc51_LblockSet ends K o x g)
  (hQ : Q ∈ gc51_RblockSet ends K o x y g) :
-- imply
  (L ∆ Q) ⊆ univ \ K ∧ sources ends (L ∆ Q) = ({y, g} : Finset W) ∧ (L ∆ (L ∆ Q)) ∈ gc51_RblockSet ends K o x y g := by
-- proof
  apply StatMech.Walls.gc52_selector_complete ends K hL hQ

/--
[gc52_switchInjective_of_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc52switchinj.lean)
-/
@[path]
private lemma gc52_switchInjective_of_card_le_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (hcard : #(gc51_LblockSet ends K o x g) ≤ #(gc51_RblockSet ends K o x y g)) :
-- imply
  gc51_SwitchInjective ends K o x y g := by
-- proof
  apply StatMech.Walls.gc52_switchInjective_of_card_le ends K hcard

/--
[gc52_card_le_of_switchInjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc52switchinj.lean)
-/
@[path]
private lemma gc52_card_le_of_switchInjective_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (h : gc51_SwitchInjective ends K o x y g) :
-- imply
  #(gc51_LblockSet ends K o x g) ≤ #(gc51_RblockSet ends K o x y g) := by
-- proof
  apply StatMech.Walls.gc52_card_le_of_switchInjective ends K h

/--
[gc52_switchInjective_iff_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc52switchinj.lean)
-/
@[path]
private lemma gc52_switchInjective_iff_card_le_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W} :
-- imply
  gc51_SwitchInjective ends K o x y g ↔ #(gc51_LblockSet ends K o x g) ≤ #(gc51_RblockSet ends K o x y g) := by
-- proof
  apply StatMech.Walls.gc52_switchInjective_iff_card_le ends K

/--
[gc52_switchInjective_iff_gc50_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc52switchinj.lean)
-/
@[path]
private lemma gc52_switchInjective_iff_gc50_count_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W} :
-- imply
  gc51_SwitchInjective ends K o x y g ↔ gc50_Lblock ends K o x g ≤ gc50_Rblock ends K o x y g := by
-- proof
  apply StatMech.Walls.gc52_switchInjective_iff_gc50_count ends K

/--
[gc52_perKCount_iff_perKDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc52switchinj.lean)
-/
@[path]
private lemma gc52_perKCount_iff_perKDom_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W} :
-- imply
  gc52_PerKCount ends o x y g ↔ gc50_PerKDom ends o x y g := by
-- proof
  apply StatMech.Walls.gc52_perKCount_iff_perKDom ends

/--
[gc52_switchInjective_of_perKCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc52switchinj.lean)
-/
@[path]
private lemma gc52_switchInjective_of_perKCount_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (h : gc52_PerKCount ends o x y g) :
-- imply
  ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc51_SwitchInjective ends K o x y g := by
-- proof
  apply StatMech.Walls.gc52_switchInjective_of_perKCount ends h

/--
[gc52_countIneq_of_perKCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc52switchinj.lean)
-/
@[path]
private lemma gc52_countIneq_of_perKCount_eq
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
  (h : gc52_PerKCount ends o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc52_countIneq_of_perKCount ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc52_witness_count_K13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc52switchinj.lean)
-/
@[path]
private lemma gc52_witness_count_K13_eq :
-- imply
  #(gc51_LblockSet gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 3) ≤ #(gc51_RblockSet gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3) := by
-- proof
  apply StatMech.Walls.gc52_witness_count_K13

/--
[gc52_witness_count_K23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc52switchinj.lean)
-/
@[path]
private lemma gc52_witness_count_K23_eq :
-- imply
  #(gc51_LblockSet gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 3) ≤ #(gc51_RblockSet gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3) := by
-- proof
  apply StatMech.Walls.gc52_witness_count_K23

/--
[gc52_witness_switchInjective_K13_via_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc52switchinj.lean)
-/
@[path]
private lemma gc52_witness_switchInjective_K13_via_count_eq :
-- imply
  gc51_SwitchInjective gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc52_witness_switchInjective_K13_via_count

/--
[gc52_witness_switchInjective_K23_via_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc52switchinj.lean)
-/
@[path]
private lemma gc52_witness_switchInjective_K23_via_count_eq :
-- imply
  gc51_SwitchInjective gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc52_witness_switchInjective_K23_via_count

/--
[gc52_witness_perKDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc52switchinj.lean)
-/
@[path]
private lemma gc52_witness_perKDom_eq :
-- imply
  gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc52_witness_perKDom


-- created on 2026-10-23
