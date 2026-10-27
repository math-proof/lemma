import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc53count.Part3
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc53_ox_conn_of_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc53count.lean)
-/
@[path]
private lemma gc53_ox_conn_of_sources_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hKsrc : sources ends K = ({o, x} : Finset W)) :
-- imply
  connK ends K o x := by
-- proof
  apply StatMech.Walls.gc53_ox_conn_of_sources ends hnd K hox hKsrc

/--
[gc53_allConn_iff_xg_gate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc53count.lean)
-/
@[path]
private lemma gc53_allConn_iff_xg_gate_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K Q : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hyg : y ≠ g)
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hQsrc : sources ends Q = ({y, g} : Finset W)) :
-- imply
  (connK ends (K ∪ Q) o x ∧ connK ends (K ∪ Q) o y ∧ connK ends (K ∪ Q) o g) ↔ connK ends (K ∪ Q) x g := by
-- proof
  apply StatMech.Walls.gc53_allConn_iff_xg_gate ends hnd K Q hox hyg hKsrc hQsrc

/--
[gc53_Rblock_eq_gateBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc53count.lean)
-/
@[path]
private lemma gc53_Rblock_eq_gateBlock_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hyg : y ≠ g)
  (hKsrc : sources ends K = ({o, x} : Finset W)) :
-- imply
  gc51_RblockSet ends K o x y g = (univ \ K).powerset.filter (fun Q => sources ends Q = ({y, g} : Finset W) ∧ connK ends (K ∪ Q) x g) := by
-- proof
  apply StatMech.Walls.gc53_Rblock_eq_gateBlock ends hnd K hox hyg hKsrc

/--
[gc53_exists_fixedPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc53count.lean)
-/
@[path]
private lemma gc53_exists_fixedPath_eq
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
  ∃ P₀, P₀ ⊆ univ \ K ∧ sources ends P₀ = ({y, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc53_exists_fixedPath ends hnd K hoy hog hxy hxg hyg huniv hKsrc

/--
[gc53_Rblock_card_eq_cosetGate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc53count.lean)
-/
@[path]
private lemma gc53_Rblock_card_eq_cosetGate_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
  {P₀ : Finset ι}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hyg : y ≠ g)
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hP₀sub : P₀ ⊆ univ \ K)
  (hP₀src : sources ends P₀ = ({y, g} : Finset W)) :
-- imply
  #(gc51_RblockSet ends K o x y g) = #(gc53_cosetGateBlock ends K P₀ o x g) := by
-- proof
  apply StatMech.Walls.gc53_Rblock_card_eq_cosetGate ends hnd K hox hyg hKsrc hP₀sub hP₀src

/--
[gc53_LblockSet_eq_gateBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc53count.lean)
-/
@[path]
private lemma gc53_LblockSet_eq_gateBlock_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x g : W} :
-- imply
  gc51_LblockSet ends K o x g = (univ \ K).powerset.filter (fun L => sources ends L = (∅ : Finset W) ∧ connK ends (K ∪ L) x g) := by
-- proof
  apply StatMech.Walls.gc53_LblockSet_eq_gateBlock ends K o x g

/--
[gc53_Lblock_le_Rblock_of_cosetGateDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc53count.lean)
-/
@[path]
private lemma gc53_Lblock_le_Rblock_of_cosetGateDom_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
  {K : Finset ι}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (hdom : gc53_CosetGateDom ends o x y g)
  (hK : K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W))) :
-- imply
  #(gc51_LblockSet ends K o x g) ≤ #(gc51_RblockSet ends K o x y g) := by
-- proof
  apply StatMech.Walls.gc53_Lblock_le_Rblock_of_cosetGateDom ends hnd hox hoy hog hxy hxg hyg huniv hdom K hK

/--
[gc53_perKCount_of_cosetGateDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc53count.lean)
-/
@[path]
private lemma gc53_perKCount_of_cosetGateDom_eq
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
  (hdom : gc53_CosetGateDom ends o x y g) :
-- imply
  gc52_PerKCount ends o x y g := by
-- proof
  apply StatMech.Walls.gc53_perKCount_of_cosetGateDom ends hnd hox hoy hog hxy hxg hyg huniv hdom

/--
[gc53_countIneq_of_cosetGateDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc53count.lean)
-/
@[path]
private lemma gc53_countIneq_of_cosetGateDom_eq
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
  (hdom : gc53_CosetGateDom ends o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc53_countIneq_of_cosetGateDom ends hnd hox hoy hog hxy hxg hyg huniv hdom

/--
[gc53_witness_cosetGateDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc53count.lean)
-/
@[path]
private lemma gc53_witness_cosetGateDom_eq :
-- imply
  gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc53_witness_cosetGateDom

/--
[gc53_witness_perKCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc53count.lean)
-/
@[path]
private lemma gc53_witness_perKCount_eq :
-- imply
  gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc53_witness_perKCount

/--
[gc53_witness_Rblock_gate_K13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc53count.lean)
-/
@[path]
private lemma gc53_witness_Rblock_gate_K13_eq :
-- imply
  gc51_RblockSet gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 = (univ \ ({1, 3} : Finset (Fin 4))).powerset.filter (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4)) ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 1 3) := by
-- proof
  apply StatMech.Walls.gc53_witness_Rblock_gate_K13


-- created on 2026-10-23
