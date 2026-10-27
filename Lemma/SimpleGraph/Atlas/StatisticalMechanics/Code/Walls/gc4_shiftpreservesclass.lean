import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc4_shiftpreservesclass
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc4_conn_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_shiftpreservesclass.lean)
-/
@[path]
private lemma gc4_conn_trichotomy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V} :
-- imply
  aie_allConn ends m o x y ∨ aie_noneConn ends m o x y ∨ gc4_exactlyOneConn ends m o x y := by
-- proof
  apply StatMech.Walls.gc4_conn_trichotomy ends m o x y

/--
[gc4_conn_classes_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_shiftpreservesclass.lean)
-/
@[path]
private lemma gc4_conn_classes_disjoint_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hall : aie_allConn ends m o x y)
  (hnone : aie_noneConn ends m o x y) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.gc4_conn_classes_disjoint ends m hall hnone

/--
[gc4_exactlyOne_not_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_shiftpreservesclass.lean)
-/
@[path]
private lemma gc4_exactlyOne_not_all_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (h : gc4_exactlyOneConn ends m o x y) :
-- imply
  ¬ aie_allConn ends m o x y := by
-- proof
  apply StatMech.Walls.gc4_exactlyOne_not_all ends m h

/--
[gc4_exactlyOne_not_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_shiftpreservesclass.lean)
-/
@[path]
private lemma gc4_exactlyOne_not_none_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (h : gc4_exactlyOneConn ends m o x y) :
-- imply
  ¬ aie_noneConn ends m o x y := by
-- proof
  apply StatMech.Walls.gc4_exactlyOne_not_none ends m h

/--
[gc4_shift_mapsTo_super](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_shiftpreservesclass.lean)
-/
@[path]
private lemma gc4_shift_mapsTo_super_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {A : Finset V}
-- given
  (hK : K ⊆ m) :
-- imply
  Set.MapsTo (fun N => N ∆ K) {N | N ⊆ m ∧ sources ends N = A} {N | N ⊆ m} := by
-- proof
  apply StatMech.Walls.gc4_shift_mapsTo_super ends m K hK A

/--
[gc4_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_shiftpreservesclass.lean)
-/
@[path]
private lemma gc4_shift_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m P Q : Finset ι}
  {A : Finset V}
-- given
  (hP : P ⊆ m)
  (hQ : Q ⊆ m) :
-- imply
  Set.MapsTo (fun N => (N ∆ P) ∆ Q) {N | N ⊆ m ∧ sources ends N = A} {N | N ⊆ m} := by
-- proof
  apply StatMech.Walls.gc4_shift ends m P Q hP hQ A

/--
[gc4_shift_image_subset_powerset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_shiftpreservesclass.lean)
-/
@[path]
private lemma gc4_shift_image_subset_powerset_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {A : Finset V}
-- given
  (hK : K ⊆ m) :
-- imply
  (m.powerset.filter (fun N => sources ends N = A)).image (fun N => N ∆ K) ⊆ m.powerset := by
-- proof
  apply StatMech.Walls.gc4_shift_image_subset_powerset ends m K hK A

/--
[gc4_shift_preserves_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_shiftpreservesclass.lean)
-/
@[path]
private lemma gc4_shift_preserves_allConn_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {A : Finset V}
  {o x y : V}
-- given
  (hK : K ⊆ m) :
-- imply
  (aie_allConn ends m o x y ↔ aie_allConn ends m o x y) ∧ Set.MapsTo (fun N => N ∆ K) {N | N ⊆ m ∧ sources ends N = A} {N | N ⊆ m} := by
-- proof
  apply StatMech.Walls.gc4_shift_preserves_allConn ends m K hK A

/--
[gc4_shift_preserves_noneConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_shiftpreservesclass.lean)
-/
@[path]
private lemma gc4_shift_preserves_noneConn_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {A : Finset V}
  {o x y : V}
-- given
  (hK : K ⊆ m) :
-- imply
  (aie_noneConn ends m o x y ↔ aie_noneConn ends m o x y) ∧ Set.MapsTo (fun N => N ∆ K) {N | N ⊆ m ∧ sources ends N = A} {N | N ⊆ m} := by
-- proof
  apply StatMech.Walls.gc4_shift_preserves_noneConn ends m K hK A

/--
[gc4_shift_preserves_exactlyOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_shiftpreservesclass.lean)
-/
@[path]
private lemma gc4_shift_preserves_exactlyOne_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {A : Finset V}
  {o x y : V}
-- given
  (hK : K ⊆ m) :
-- imply
  (gc4_exactlyOneConn ends m o x y ↔ gc4_exactlyOneConn ends m o x y) ∧ Set.MapsTo (fun N => N ∆ K) {N | N ⊆ m ∧ sources ends N = A} {N | N ⊆ m} := by
-- proof
  apply StatMech.Walls.gc4_shift_preserves_exactlyOne ends m K hK A

/--
[gc4_shift_preserves_backboneFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_shiftpreservesclass.lean)
-/
@[path]
private lemma gc4_shift_preserves_backboneFactor_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {A : Finset V}
  {o x y : V}
-- given
  (hK : K ⊆ m) :
-- imply
  asd_ghsBackboneFactor ends m o x y = asd_ghsBackboneFactor ends m o x y ∧ Set.MapsTo (fun N => N ∆ K) {N | N ⊆ m ∧ sources ends N = A} {N | N ⊆ m} := by
-- proof
  apply StatMech.Walls.gc4_shift_preserves_backboneFactor ends m K hK A o x y

/--
[gc4_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_shiftpreservesclass.lean)
-/
@[path]
private lemma gc4_shift_eq_2
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m P Q : Finset ι}
  {A : Finset V}
  {o x y : V}
-- given
  (hP : P ⊆ m)
  (hQ : Q ⊆ m) :
-- imply
  (aie_allConn ends m o x y ↔ aie_allConn ends m o x y) ∧ (aie_noneConn ends m o x y ↔ aie_noneConn ends m o x y) ∧ (gc4_exactlyOneConn ends m o x y ↔ gc4_exactlyOneConn ends m o x y) ∧ Set.MapsTo (fun N => (N ∆ P) ∆ Q) {N | N ⊆ m ∧ sources ends N = A} {N | N ⊆ m} := by
-- proof
  apply StatMech.Walls.gc4_shift ends m P Q hP hQ A o x y

/--
[gc4_shift_member_same_class](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_shiftpreservesclass.lean)
-/
@[path]
private lemma gc4_shift_member_same_class_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {A : Finset V}
  {o x y : V}
  {N : Finset ι}
-- given
  (hK : K ⊆ m)
  (hN : N ⊆ m ∧ sources ends N = A) :
-- imply
  (N ∆ K) ⊆ m ∧ ((aie_allConn ends m o x y ∧ aie_allConn ends m o x y) ∨ (aie_noneConn ends m o x y ∧ aie_noneConn ends m o x y) ∨ (gc4_exactlyOneConn ends m o x y ∧ gc4_exactlyOneConn ends m o x y)) := by
-- proof
  apply StatMech.Walls.gc4_shift_member_same_class ends m K hK A hN

/--
[gc4_twoSourceSwitch_preserves_class](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_shiftpreservesclass.lean)
-/
@[path]
private lemma gc4_twoSourceSwitch_preserves_class_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m P Q : Finset ι}
  {A : Finset V}
  {u v s t : V}
  {o x y : V}
-- given
  (hP : P ⊆ m)
  (hQ : Q ⊆ m)
  (huv : u ≠ v)
  (hst : s ≠ t)
  (hconnuv : connK ends m u v)
  (hconnst : connK ends m s t) :
-- imply
  #(m.powerset.filter (fun K => sources ends K = A ∆ {u, v} ∆ {s, t})) = #(m.powerset.filter (fun K => sources ends K = A)) ∧ (aie_allConn ends m o x y ↔ aie_allConn ends m o x y) ∧ (aie_noneConn ends m o x y ↔ aie_noneConn ends m o x y) ∧ (gc4_exactlyOneConn ends m o x y ↔ gc4_exactlyOneConn ends m o x y) ∧ Set.MapsTo (fun K => (K ∆ P) ∆ Q) {K | K ⊆ m ∧ sources ends K = A} {K | K ⊆ m} := by
-- proof
  apply StatMech.Walls.gc4_twoSourceSwitch_preserves_class ends m P Q hP hQ A huv hst hconnuv hconnst o x y

/--
[gc4_shift_witness_in_super](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_shiftpreservesclass.lean)
-/
@[path]
private lemma gc4_shift_witness_in_super_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m K : Finset ι}
  {A : Finset V}
  {N₀ : Finset ι}
-- given
  (hK : K ⊆ m)
  (hN₀m : N₀ ⊆ m)
  (hN₀A : sources ends N₀ = A) :
-- imply
  (N₀ ∆ K) ⊆ m ∧ asd_ghsBackboneFactor ends m = asd_ghsBackboneFactor ends m := by
-- proof
  apply StatMech.Walls.gc4_shift_witness_in_super ends m K hK A hN₀m hN₀A

/--
[gc4_class_indep_of_subconfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_shiftpreservesclass.lean)
-/
@[path]
private lemma gc4_class_indep_of_subconfig_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
  {N₁ N₂ : Finset ι} :
-- imply
  (aie_allConn ends m o x y ↔ aie_allConn ends m o x y) ∧ (aie_noneConn ends m o x y ↔ aie_noneConn ends m o x y) ∧ (gc4_exactlyOneConn ends m o x y ↔ gc4_exactlyOneConn ends m o x y) := by
-- proof
  apply StatMech.Walls.gc4_class_indep_of_subconfig ends m o x y N₁ N₂


-- created on 2026-10-23
