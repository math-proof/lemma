import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc51minpath.Part4
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc51_connK_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_connK_mono_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K₁ K₂ : Finset ι}
  {a b : W}
-- given
  (h : K₁ ⊆ K₂)
  (hab : connK ends K₁ a b) :
-- imply
  connK ends K₂ a b := by
-- proof
  apply StatMech.Walls.gc51_connK_mono ends h hab

/--
[gc51_connK_of_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_connK_of_sources_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {P : Finset ι}
  {y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hyg : y ≠ g)
  (hPsrc : sources ends P = ({y, g} : Finset W)) :
-- imply
  connK ends P y g := by
-- proof
  apply StatMech.Walls.gc51_connK_of_sources ends hnd P hyg hPsrc

/--
[gc51_sdiff_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_sdiff_sources_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {V L : Finset ι}
  {y g : W}
-- given
  (hLV : L ⊆ V)
  (hVsrc : sources ends V = ({y, g} : Finset W))
  (hLsrc : sources ends L = (∅ : Finset W)) :
-- imply
  sources ends (V \ L) = ({y, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc51_sdiff_sources ends hLV hVsrc hLsrc

/--
[gc51_exists_remPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_exists_remPath_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {V L : Finset ι}
  {y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hLV : L ⊆ V)
  (hyg : y ≠ g)
  (hVsrc : sources ends V = ({y, g} : Finset W))
  (hLsrc : sources ends L = (∅ : Finset W)) :
-- imply
  ∃ P, P ⊆ V \ L ∧ sources ends P = ({y, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc51_exists_remPath ends hnd hLV hyg hVsrc hLsrc

/--
[gc51_remPath_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_remPath_disjoint_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [DecidableEq ι]
  {V L P : Finset ι}
-- given
  (hP : P ⊆ V \ L) :
-- imply
  Disjoint L P := by
-- proof
  apply StatMech.Walls.gc51_remPath_disjoint hP

/--
[gc51_mapsInto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_mapsInto_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
  {V L P : Finset ι}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hyg : y ≠ g)
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hLV : L ⊆ V)
  (hPVL : P ⊆ V \ L)
  (hLsrc : sources ends L = (∅ : Finset W))
  (hPsrc : sources ends P = ({y, g} : Finset W))
  (hgate : connK ends (K ∪ L) x g) :
-- imply
  (L ∪ P) ⊆ V ∧ sources ends (L ∪ P) = ({y, g} : Finset W) ∧ connK ends (K ∪ (L ∪ P)) o x ∧ connK ends (K ∪ (L ∪ P)) o y ∧ connK ends (K ∪ (L ∪ P)) o g := by
-- proof
  apply StatMech.Walls.gc51_mapsInto ends hnd K hox hyg hKsrc hLV hPVL hLsrc hPsrc hgate

/--
[gc51_LblockSet_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_LblockSet_card_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x g : W} :
-- imply
  #(gc51_LblockSet ends K o x g) = gc50_Lblock ends K o x g := by
-- proof
  apply StatMech.Walls.gc51_LblockSet_card ends K o x g

/--
[gc51_RblockSet_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_RblockSet_card_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W} :
-- imply
  #(gc51_RblockSet ends K o x y g) = gc50_Rblock ends K o x y g := by
-- proof
  apply StatMech.Walls.gc51_RblockSet_card ends K o x y g

/--
[gc51_perK_dom_of_switchInjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_perK_dom_of_switchInjective_eq
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
  gc50_Lblock ends K o x g ≤ gc50_Rblock ends K o x y g := by
-- proof
  apply StatMech.Walls.gc51_perK_dom_of_switchInjective ends K h

/--
[gc51_disjoint_mapsInto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_disjoint_mapsInto_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
  {L P : Finset ι}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hyg : y ≠ g)
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hL : L ∈ gc51_LblockSet ends K o x g)
  (hPVL : P ⊆ (univ \ K) \ L)
  (hPsrc : sources ends P = ({y, g} : Finset W)) :
-- imply
  (L ∆ P) ∈ gc51_RblockSet ends K o x y g := by
-- proof
  apply StatMech.Walls.gc51_disjoint_mapsInto ends hnd K hox hyg hKsrc hL hPVL hPsrc

/--
[gc51_complSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_complSources_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (hKsrc : sources ends K = ({o, x} : Finset W)) :
-- imply
  sources ends (univ \ K) = ({y, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc51_complSources ends K hoy hog hxy hxg huniv hKsrc

/--
[gc51_perKDom_of_switchInjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_perKDom_of_switchInjective_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc51_SwitchInjective ends K o x y g) :
-- imply
  gc50_PerKDom ends o x y g := by
-- proof
  apply StatMech.Walls.gc51_perKDom_of_switchInjective ends h

/--
[gc51_countIneq_of_switchInjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_countIneq_of_switchInjective_eq
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
  (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc51_SwitchInjective ends K o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc51_countIneq_of_switchInjective ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc51_witness_LblockSet_K13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_witness_LblockSet_K13_eq :
-- imply
  gc51_LblockSet gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 3 = {(∅ : Finset (Fin 4))} := by
-- proof
  apply StatMech.Walls.gc51_witness_LblockSet_K13

/--
[gc51_witness_LblockSet_K23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_witness_LblockSet_K23_eq :
-- imply
  gc51_LblockSet gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 3 = {(∅ : Finset (Fin 4))} := by
-- proof
  apply StatMech.Walls.gc51_witness_LblockSet_K23

/--
[gc51_witness_RblockSet_K13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_witness_RblockSet_K13_eq :
-- imply
  gc51_RblockSet gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 = {({0, 2} : Finset (Fin 4))} := by
-- proof
  apply StatMech.Walls.gc51_witness_RblockSet_K13

/--
[gc51_witness_RblockSet_K23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_witness_RblockSet_K23_eq :
-- imply
  gc51_RblockSet gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 = {({0, 1} : Finset (Fin 4))} := by
-- proof
  apply StatMech.Walls.gc51_witness_RblockSet_K23

/--
[gc51_witness_switchInjective_K13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_witness_switchInjective_K13_eq :
-- imply
  gc51_SwitchInjective gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc51_witness_switchInjective_K13

/--
[gc51_witness_switchInjective_K23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_witness_switchInjective_K23_eq :
-- imply
  gc51_SwitchInjective gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc51_witness_switchInjective_K23

/--
[gc51_witness_perKDom_via_switchInjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_witness_perKDom_via_switchInjective_eq :
-- imply
  gc50_PerKDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc51_witness_perKDom_via_switchInjective

/--
[gc51_witness_EMassResidue_via_switchInjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_witness_EMassResidue_via_switchInjective_eq :
-- imply
  gc42_EMassResidue gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc51_witness_EMassResidue_via_switchInjective

/--
[gc51_ceEnds_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_ceEnds_univ_sources_eq :
-- imply
  sources gc51_ceEnds (univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc51_ceEnds_univ_sources

/--
[gc51_ce_Rblock_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_ce_Rblock_zero_eq :
-- imply
  gc50_Rblock gc51_ceEnds ({0, 1} : Finset (Fin 2)) 0 1 2 3 = 0 := by
-- proof
  apply StatMech.Walls.gc51_ce_Rblock_zero

/--
[gc51_ce_Lblock_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_ce_Lblock_one_eq :
-- imply
  gc50_Lblock gc51_ceEnds ({0, 1} : Finset (Fin 2)) 0 1 3 = 1 := by
-- proof
  apply StatMech.Walls.gc51_ce_Lblock_one

/--
[gc51_perKDom_false_without_huniv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean)
-/
@[path]
private lemma gc51_perKDom_false_without_huniv_eq :
-- imply
  ¬ gc50_PerKDom gc51_ceEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc51_perKDom_false_without_huniv


-- created on 2026-10-23
