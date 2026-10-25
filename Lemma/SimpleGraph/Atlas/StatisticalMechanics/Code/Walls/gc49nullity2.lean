import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc49nullity2.Part3
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc49_sd_oxyg_yg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_sd_oxyg_yg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {o x y g : W}
-- given
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g) :
-- imply
  ({o, x, y, g} : Finset W) ∆ ({y, g} : Finset W) = ({o, x} : Finset W) := by
-- proof
  apply StatMech.Walls.gc49_sd_oxyg_yg hoy hog hxy hxg

/--
[gc49_complSubUniverse_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_complSubUniverse_sources_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
  {n₁ : Finset ι}
-- given
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (hn₁ : sources ends n₁ = (∅ : Finset W)) :
-- imply
  sources ends (univ \ n₁) = ({o, x, y, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc49_complSubUniverse_sources ends huniv hn₁

/--
[gc49_switching_ox_of_oxyg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_switching_ox_of_oxyg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {V : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ V, ¬ (ends i).IsDiag)
  (hVsrc : sources ends V = ({o, x, y, g} : Finset W))
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g) :
-- imply
  #(V.powerset.filter (fun K => sources ends K = ({o, x} : Finset W))) = (if connK ends V y g then #(V.powerset.filter (fun K => sources ends K = ({o, x, y, g} : Finset W))) else 0) := by
-- proof
  apply StatMech.Walls.gc49_switching_ox_of_oxyg ends V hnd hVsrc hoy hog hxy hxg hyg

/--
[gc49_LHSdoubled_card_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_LHSdoubled_card_eq_sum_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W} :
-- imply
  #(gc48_LHSdoubled ends o x y g) = ∑ n₁ ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = (∅ : Finset W)), #((univ \ n₁).powerset.filter (fun n₂ => sources ends n₂ = ({o, x} : Finset W) ∧ connK ends (n₁ ∪ n₂) x g)) := by
-- proof
  apply StatMech.Walls.gc49_LHSdoubled_card_eq_sum ends o x y g

/--
[gc49_RHSdoubled_card_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_RHSdoubled_card_eq_sum_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W} :
-- imply
  #(gc48_RHSdoubled ends o x y g) = ∑ n₁ ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = (∅ : Finset W)), #((univ \ n₁).powerset.filter (fun m₂ => sources ends m₂ = ({o, x, y, g} : Finset W) ∧ connK ends (n₁ ∪ m₂) o x ∧ connK ends (n₁ ∪ m₂) o y ∧ connK ends (n₁ ∪ m₂) o g)) := by
-- proof
  apply StatMech.Walls.gc49_RHSdoubled_card_eq_sum ends o x y g

/--
[gc49_doubled_le_of_innerDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_doubled_le_of_innerDom_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (h : gc49_InnerDom ends o x y g) :
-- imply
  #(gc48_LHSdoubled ends o x y g) ≤ #(gc48_RHSdoubled ends o x y g) := by
-- proof
  apply StatMech.Walls.gc49_doubled_le_of_innerDom ends o x y g h

/--
[gc49_EMassResidue_of_innerDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_EMassResidue_of_innerDom_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (h : gc49_InnerDom ends o x y g) :
-- imply
  gc42_EMassResidue ends o x y g := by
-- proof
  apply StatMech.Walls.gc49_EMassResidue_of_innerDom ends o x y g h

/--
[gc49_innerDom_iff_EMassResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_innerDom_iff_EMassResidue_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W} :
-- imply
  gc49_InnerDom ends o x y g ↔ gc42_EMassResidue ends o x y g := by
-- proof
  apply StatMech.Walls.gc49_innerDom_iff_EMassResidue ends o x y g

/--
[gc49_countIneq_of_innerDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_countIneq_of_innerDom_eq
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
  (h : gc49_InnerDom ends o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc49_countIneq_of_innerDom ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc49_witnessEnds_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_witnessEnds_loopless_eq :
-- imply
  ∀ i : Fin 4, ¬ (gc49_witnessEnds i).IsDiag := by
-- proof
  apply StatMech.Walls.gc49_witnessEnds_loopless

/--
[gc49_witnessEnds_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_witnessEnds_univ_sources_eq :
-- imply
  sources gc49_witnessEnds (univ : Finset (Fin 4)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc49_witnessEnds_univ_sources

/--
[gc49_witness_Lset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_witness_Lset_eq :
-- imply
  gc43_Lset gc49_witnessEnds (0 : Fin 4) 1 2 3 = {({1, 3} : Finset (Fin 4)), {2, 3}} := by
-- proof
  apply StatMech.Walls.gc49_witness_Lset

/--
[gc49_witness_Rset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_witness_Rset_eq :
-- imply
  gc43_Rset gc49_witnessEnds (0 : Fin 4) 1 2 3 = {(univ : Finset (Fin 4))} := by
-- proof
  apply StatMech.Walls.gc49_witness_Rset

/--
[gc49_witness_EMassResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_witness_EMassResidue_eq :
-- imply
  gc42_EMassResidue gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc49_witness_EMassResidue

/--
[gc49_witness_innerL_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_witness_innerL_empty_eq :
-- imply
  #(((univ : Finset (Fin 4)) \ ∅).powerset.filter (fun n₂ => sources gc49_witnessEnds n₂ = ({0, 1} : Finset (Fin 4)) ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ n₂) 1 3)) = 2 := by
-- proof
  apply StatMech.Walls.gc49_witness_innerL_empty

/--
[gc49_witness_innerR_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_witness_innerR_empty_eq :
-- imply
  #(((univ : Finset (Fin 4)) \ ∅).powerset.filter (fun m₂ => sources gc49_witnessEnds m₂ = ({0, 1, 2, 3} : Finset (Fin 4)) ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 1 ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 2 ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 3)) = 1 := by
-- proof
  apply StatMech.Walls.gc49_witness_innerR_empty

/--
[gc49_perN1Dom_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_perN1Dom_false_eq :
-- imply
  #(((univ : Finset (Fin 4)) \ ∅).powerset.filter (fun n₂ => sources gc49_witnessEnds n₂ = ({0, 1} : Finset (Fin 4)) ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ n₂) 1 3)) > #(((univ : Finset (Fin 4)) \ ∅).powerset.filter (fun m₂ => sources gc49_witnessEnds m₂ = ({0, 1, 2, 3} : Finset (Fin 4)) ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 1 ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 2 ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 3)) := by
-- proof
  apply StatMech.Walls.gc49_perN1Dom_false

/--
[gc49_residue_is_aggregate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_residue_is_aggregate_eq :
-- imply
  gc42_EMassResidue gc49_witnessEnds (0 : Fin 4) 1 2 3 ∧ #(((univ : Finset (Fin 4)) \ ∅).powerset.filter (fun n₂ => sources gc49_witnessEnds n₂ = ({0, 1} : Finset (Fin 4)) ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ n₂) 1 3)) > #(((univ : Finset (Fin 4)) \ ∅).powerset.filter (fun m₂ => sources gc49_witnessEnds m₂ = ({0, 1, 2, 3} : Finset (Fin 4)) ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 1 ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 2 ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 3)) := by
-- proof
  apply StatMech.Walls.gc49_residue_is_aggregate

/--
[gc49_diamond_conn_yg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_diamond_conn_yg_eq :
-- imply
  connK gc45_diamondEnds (univ : Finset (Fin 4)) 2 3 := by
-- proof
  apply StatMech.Walls.gc49_diamond_conn_yg

/--
[gc49_diamond_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_diamond_switching_eq :
-- imply
  #((univ : Finset (Fin 4)).powerset.filter (fun K => sources gc45_diamondEnds K = ({0, 1} : Finset (Fin 4)))) = #((univ : Finset (Fin 4)).powerset.filter (fun K => sources gc45_diamondEnds K = ({0, 1, 2, 3} : Finset (Fin 4)))) := by
-- proof
  apply StatMech.Walls.gc49_diamond_switching

/--
[gc49_diamond_innerDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_diamond_innerDom_eq :
-- imply
  gc49_InnerDom gc45_diamondEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc49_diamond_innerDom

/--
[gc49_diamond_countIneq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc49nullity2.lean)
-/
@[path]
private lemma gc49_diamond_countIneq_eq :
-- imply
  gc39_ThreeColouringCountIneq gc45_diamondEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc49_diamond_countIneq


-- created on 2026-10-23
