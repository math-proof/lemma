import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc50threereplica.Part3
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc50_sd_ox_ox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_sd_ox_ox_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {o x : W} :
-- imply
  ({o, x} : Finset W) ∆ ({o, x} : Finset W) = (∅ : Finset W) := by
-- proof
  apply StatMech.Walls.gc50_sd_ox_ox

/--
[gc50_sd_oxyg_yg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_sd_oxyg_yg_eq
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
  apply StatMech.Walls.gc50_sd_oxyg_yg hoy hog hxy hxg

/--
[gc50_E_eq_oxCount_of_ox_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_E_eq_oxCount_of_ox_conn_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x : W}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hm : sources ends m = ({o, x} : Finset W)) :
-- imply
  gc40_E ends m = #(m.powerset.filter (fun K => sources ends K = ({o, x} : Finset W))) := by
-- proof
  apply StatMech.Walls.gc50_E_eq_oxCount_of_ox_conn ends m hnd hox hm

/--
[gc50_sd_empty_og_xg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_sd_empty_og_xg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {o x g : W}
-- given
  (hox : o ≠ x)
  (hog : o ≠ g)
  (hxg : x ≠ g) :
-- imply
  ((∅ : Finset W) ∆ ({o, g} : Finset W)) ∆ ({x, g} : Finset W) = ({o, x} : Finset W) := by
-- proof
  apply StatMech.Walls.gc50_sd_empty_og_xg hox hog hxg

/--
[gc50_E_eq_oxCount_of_all_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_E_eq_oxCount_of_all_conn_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x g : W}
-- given
  (hox : o ≠ x)
  (hog : o ≠ g)
  (hxg : x ≠ g)
  (hconn_ox : connK ends m o x)
  (hconn_og : connK ends m o g) :
-- imply
  gc40_E ends m = #(m.powerset.filter (fun K => sources ends K = ({o, x} : Finset W))) := by
-- proof
  apply StatMech.Walls.gc50_E_eq_oxCount_of_all_conn ends m hox hog hxg hconn_ox hconn_og

/--
[gc50_reindex_by_oxCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_reindex_by_oxCurrent_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x : W}
  {B Bmox : Finset W}
  [DecidablePred G]
-- given
  (hBmox : B ∆ ({o, x} : Finset W) = Bmox)
  (G : Finset ι → Prop) :
-- imply
  #(((univ : Finset ι).powerset.filter (fun m => sources ends m = B ∧ G m)).sigma (fun m => m.powerset.filter (fun K => sources ends K = ({o, x} : Finset W)))) = ∑ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), #((univ \ K).powerset.filter (fun R => sources ends R = Bmox ∧ G (K ∪ R))) := by
-- proof
  apply StatMech.Walls.gc50_reindex_by_oxCurrent ends o x B Bmox hBmox G

/--
[gc50_LHS_eq_perKsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_LHS_eq_perKsum_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x) :
-- imply
  (∑ m ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x} : Finset W)), (if connK ends m x g then gc40_E ends m else 0)) = ∑ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc50_Lblock ends K o x g := by
-- proof
  apply StatMech.Walls.gc50_LHS_eq_perKsum ends hnd hox

/--
[gc50_sd_oxyg_ox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_sd_oxyg_ox_eq
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
  ({o, x, y, g} : Finset W) ∆ ({o, x} : Finset W) = ({y, g} : Finset W) := by
-- proof
  apply StatMech.Walls.gc50_sd_oxyg_ox hoy hog hxy hxg

/--
[gc50_RHS_eq_perKsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_RHS_eq_perKsum_eq
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
  (hxg : x ≠ g) :
-- imply
  (∑ m ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x, y, g} : Finset W)), (if connK ends m o x ∧ connK ends m o y ∧ connK ends m o g then gc40_E ends m else 0)) = ∑ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc50_Rblock ends K o x y g := by
-- proof
  apply StatMech.Walls.gc50_RHS_eq_perKsum ends hnd hox hoy hog hxy hxg

/--
[gc50_EMassResidue_of_perKDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_EMassResidue_of_perKDom_eq
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
  (h : gc50_PerKDom ends o x y g) :
-- imply
  gc42_EMassResidue ends o x y g := by
-- proof
  apply StatMech.Walls.gc50_EMassResidue_of_perKDom ends hnd hox hoy hog hxy hxg h

/--
[gc50_EMassResidue_iff_perKsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_EMassResidue_iff_perKsum_eq
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
  (hxg : x ≠ g) :
-- imply
  gc42_EMassResidue ends o x y g ↔ (∑ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc50_Lblock ends K o x g) ≤ ∑ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc50_Rblock ends K o x y g := by
-- proof
  apply StatMech.Walls.gc50_EMassResidue_iff_perKsum ends hnd hox hoy hog hxy hxg

/--
[gc50_countIneq_of_perKDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_countIneq_of_perKDom_eq
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
  (h : gc50_PerKDom ends o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc50_countIneq_of_perKDom ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc50_witness_oxCurrents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_witness_oxCurrents_eq :
-- imply
  (univ : Finset (Fin 4)).powerset.filter (fun K => sources gc49_witnessEnds K = ({0, 1} : Finset (Fin 4))) = {({1, 3} : Finset (Fin 4)), {2, 3}} := by
-- proof
  apply StatMech.Walls.gc50_witness_oxCurrents

/--
[gc50_witness_Lblock_K13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_witness_Lblock_K13_eq :
-- imply
  gc50_Lblock gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 3 = 1 := by
-- proof
  apply StatMech.Walls.gc50_witness_Lblock_K13

/--
[gc50_witness_univ_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_witness_univ_allConn_eq :
-- imply
  connK gc49_witnessEnds (univ : Finset (Fin 4)) 0 1 ∧ connK gc49_witnessEnds (univ : Finset (Fin 4)) 0 2 ∧ connK gc49_witnessEnds (univ : Finset (Fin 4)) 0 3 := by
-- proof
  apply StatMech.Walls.gc50_witness_univ_allConn

/--
[gc50_witness_Rblock_K13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_witness_Rblock_K13_eq :
-- imply
  gc50_Rblock gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 = 1 := by
-- proof
  apply StatMech.Walls.gc50_witness_Rblock_K13

/--
[gc50_witness_Lblock_K23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_witness_Lblock_K23_eq :
-- imply
  gc50_Lblock gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 3 = 1 := by
-- proof
  apply StatMech.Walls.gc50_witness_Lblock_K23

/--
[gc50_witness_Rblock_K23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_witness_Rblock_K23_eq :
-- imply
  gc50_Rblock gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 = 1 := by
-- proof
  apply StatMech.Walls.gc50_witness_Rblock_K23

/--
[gc50_witness_perKDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_witness_perKDom_eq :
-- imply
  gc50_PerKDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc50_witness_perKDom

/--
[gc50_witness_EMassResidue_via_perK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_witness_EMassResidue_via_perK_eq :
-- imply
  gc42_EMassResidue gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc50_witness_EMassResidue_via_perK

/--
[gc50_perK_succeeds_where_perN1_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean)
-/
@[path]
private lemma gc50_perK_succeeds_where_perN1_fails_eq :
-- imply
  gc50_PerKDom gc49_witnessEnds (0 : Fin 4) 1 2 3 ∧ #(((univ : Finset (Fin 4)) \ ∅).powerset.filter (fun n₂ => sources gc49_witnessEnds n₂ = ({0, 1} : Finset (Fin 4)) ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ n₂) 1 3)) > #(((univ : Finset (Fin 4)) \ ∅).powerset.filter (fun m₂ => sources gc49_witnessEnds m₂ = ({0, 1, 2, 3} : Finset (Fin 4)) ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 1 ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 2 ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 3)) := by
-- proof
  apply StatMech.Walls.gc50_perK_succeeds_where_perN1_fails


-- created on 2026-10-23
