import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
open StatMech StatMech.FrontierD


/--
[finiteFirstReturnTime_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturnTime_pos_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {x : {a : A // selected a}}
-- given
  (selected : A -> Prop) :
-- imply
  0 < finiteFirstReturnTime sigma selected x := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturnTime_pos sigma selected x

/--
[finiteFirstReturnTime_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturnTime_selected_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {x : {a : A // selected a}}
-- given
  (selected : A -> Prop) :
-- imply
  selected ((sigma ^ finiteFirstReturnTime sigma selected x) x.1) := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturnTime_selected sigma selected x

/--
[finiteFirstReturnTime_minimal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturnTime_minimal_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {x : {a : A // selected a}}
  {n : Nat}
-- given
  (selected : A -> Prop)
  (hn : n < finiteFirstReturnTime sigma selected x) :
-- imply
  Not (0 < n /\ selected ((sigma ^ n) x.1)) := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturnTime_minimal sigma selected x n hn

/--
[finitePerm_pow_sub_apply_eq_of_pow_apply_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finitePerm_pow_sub_apply_eq_of_pow_apply_eq_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  {x y : A}
  {m n : Nat}
-- given
  (hmn : m <= n)
  (h : (sigma ^ m) x = (sigma ^ n) y) :
-- imply
  x = (sigma ^ (n - m)) y := by
-- proof
  apply StatMech.FrontierD.finitePerm_pow_sub_apply_eq_of_pow_apply_eq sigma x y m n hmn h

/--
[finiteFirstReturn_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturn_injective_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
-- given
  (selected : A -> Prop) :
-- imply
  Function.Injective (finiteFirstReturn sigma selected) := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturn_injective sigma selected

/--
[finiteFirstReturnPerm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturnPerm_apply_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {x : {a : A // selected a}}
-- given
  (selected : A -> Prop) :
-- imply
  finiteFirstReturnPerm sigma selected x = finiteFirstReturn sigma selected x := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturnPerm_apply sigma selected x

/--
[finiteFirstReturnPerm_pow_eq_ambient_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturnPerm_pow_eq_ambient_pow_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {x : {a : A // selected a}}
  {n : Nat}
-- given
  (selected : A -> Prop) :
-- imply
  exists k : Nat, ((finiteFirstReturnPerm sigma selected ^ n) x).1 = (sigma ^ k) x.1 := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturnPerm_pow_eq_ambient_pow sigma selected x n

/--
[finiteFirstReturnPerm_sameCycle_ambient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturnPerm_sameCycle_ambient_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {x y : {a : A // selected a}}
-- given
  (selected : A -> Prop)
  (hcycle : (finiteFirstReturnPerm sigma selected).SameCycle x y) :
-- imply
  sigma.SameCycle x.1 y.1 := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturnPerm_sameCycle_ambient sigma selected x y hcycle

/--
[length_finiteFirstReturnSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma length_finiteFirstReturnSegment_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {x : {a : A // selected a}}
-- given
  (selected : A -> Prop) :
-- imply
  (finiteFirstReturnSegment sigma selected x).length = finiteFirstReturnTime sigma selected x := by
-- proof
  apply StatMech.FrontierD.length_finiteFirstReturnSegment sigma selected x

/--
[finiteFirstReturnSegment_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturnSegment_nodup_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {x : {a : A // selected a}}
-- given
  (selected : A -> Prop) :
-- imply
  (finiteFirstReturnSegment sigma selected x).Nodup := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturnSegment_nodup sigma selected x

/--
[finiteFirstReturnSegment_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturnSegment_disjoint_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {x y : {a : A // selected a}}
-- given
  (selected : A -> Prop)
  (hxy : x ≠ y) :
-- imply
  (finiteFirstReturnSegment sigma selected x).Disjoint (finiteFirstReturnSegment sigma selected y) := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturnSegment_disjoint sigma selected x y hxy

/--
[mem_finiteFirstReturnSegments_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma mem_finiteFirstReturnSegments_iff_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {states : List {a : A // selected a}}
  {d : A}
-- given
  (selected : A -> Prop) :
-- imply
  d ∈ finiteFirstReturnSegments sigma selected states ↔ ∃ x ∈ states, ∃ k : Nat, k < finiteFirstReturnTime sigma selected x ∧ (sigma ^ k) x.1 = d := by
-- proof
  apply StatMech.FrontierD.mem_finiteFirstReturnSegments_iff sigma selected states d

/--
[mem_finiteFirstReturnSegments_step_iff_of_not_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma mem_finiteFirstReturnSegments_step_iff_of_not_selected_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {states : List {a : A // selected a}}
  {d : A}
-- given
  (selected : A -> Prop)
  (hnext : Not (selected (sigma d))) :
-- imply
  sigma d ∈ finiteFirstReturnSegments sigma selected states ↔ d ∈ finiteFirstReturnSegments sigma selected states := by
-- proof
  apply StatMech.FrontierD.mem_finiteFirstReturnSegments_step_iff_of_not_selected sigma selected states d hnext

/--
[mem_finiteFirstReturnSegments_predecessor_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma mem_finiteFirstReturnSegments_predecessor_iff_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {states : List {a : A // selected a}}
  {d : A}
  {y : {a : A // selected a}}
-- given
  (selected : A -> Prop)
  (hstep : sigma d = y.1) :
-- imply
  d ∈ finiteFirstReturnSegments sigma selected states ↔ (finiteFirstReturnPerm sigma selected).symm y ∈ states := by
-- proof
  apply StatMech.FrontierD.mem_finiteFirstReturnSegments_predecessor_iff sigma selected states d y hstep

/--
[finiteFirstReturnSegments_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturnSegments_nodup_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {states : List {a : A // selected a}}
-- given
  (selected : A -> Prop)
  (hstates : states.Nodup) :
-- imply
  (finiteFirstReturnSegments sigma selected states).Nodup := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturnSegments_nodup sigma selected states hstates

/--
[finiteFirstReturnOccurrencePoint_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturnOccurrencePoint_injective_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {states : List {a : A // selected a}}
-- given
  (selected : A -> Prop)
  (hstates : states.Nodup) :
-- imply
  Function.Injective (finiteFirstReturnOccurrencePoint sigma selected states) := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturnOccurrencePoint_injective sigma selected states hstates

/--
[finiteFirstReturnOccurrencePoint_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturnOccurrencePoint_succ_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {states : List {a : A // selected a}}
  {x : FiniteFirstReturnOccurrenceIndex sigma selected states}
-- given
  (selected : A -> Prop)
  (hnext : x.2.val + 1 < finiteFirstReturnTime sigma selected (states.get x.1)) :
-- imply
  sigma (finiteFirstReturnOccurrencePoint sigma selected states x) = finiteFirstReturnOccurrencePoint sigma selected states (finiteFirstReturnOccurrenceIndexSucc sigma selected states x hnext) := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturnOccurrencePoint_succ sigma selected states x hnext

/--
[finiteFirstReturnOccurrencePoint_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturnOccurrencePoint_last_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {states : List {a : A // selected a}}
  {x : FiniteFirstReturnOccurrenceIndex sigma selected states}
-- given
  (selected : A -> Prop)
  (hlast : x.2.val + 1 = finiteFirstReturnTime sigma selected (states.get x.1)) :
-- imply
  sigma (finiteFirstReturnOccurrencePoint sigma selected states x) = (finiteFirstReturn sigma selected (states.get x.1)).1 := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturnOccurrencePoint_last sigma selected states x hlast

/--
[finiteFirstReturnOccurrencePoint_step_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturnOccurrencePoint_step_interior_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {states : List {a : A // selected a}}
  {i : Fin states.length}
  {k : Nat}
-- given
  (selected : A -> Prop)
  (hk : k + 1 < finiteFirstReturnTime sigma selected (states.get i)) :
-- imply
  sigma (finiteFirstReturnOccurrencePoint sigma selected states ⟨i, ⟨k, by omega⟩⟩) = finiteFirstReturnOccurrencePoint sigma selected states ⟨i, ⟨k + 1, hk⟩⟩ := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturnOccurrencePoint_step_interior sigma selected states i k hk

/--
[finiteFirstReturnOccurrencePoint_step_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturnOccurrencePoint_step_endpoint_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {states : List {a : A // selected a}}
  {i : Fin states.length}
  {k : Nat}
-- given
  (selected : A -> Prop)
  (hk : k < finiteFirstReturnTime sigma selected (states.get i))
  (hlast : k + 1 = finiteFirstReturnTime sigma selected (states.get i)) :
-- imply
  sigma (finiteFirstReturnOccurrencePoint sigma selected states ⟨i, ⟨k, hk⟩⟩) = (finiteFirstReturn sigma selected (states.get i)).1 := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturnOccurrencePoint_step_endpoint sigma selected states i k hk hlast

/--
[finiteFirstReturnOccurrencePoint_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturnOccurrencePoint_zero_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {states : List {a : A // selected a}}
  {i : Fin states.length}
-- given
  (selected : A -> Prop) :
-- imply
  finiteFirstReturnOccurrencePoint sigma selected states (finiteFirstReturnOccurrenceIndexZero sigma selected states i) = (states.get i).1 := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturnOccurrencePoint_zero sigma selected states i

/--
[finiteRelated_until_firstReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteRelated_until_firstReturn_eq
  [Fintype A]
  [DecidableEq A]
  [Fintype B]
  [DecidableEq B]
  {sigma : Equiv.Perm A}
  {tau : Equiv.Perm B}
  [DecidablePred selectedA]
  [DecidablePred selectedB]
  {x : {a : A // selectedA a}}
  {y : {b : B // selectedB b}}
  {n : Nat}
-- given
  (selectedA : A -> Prop)
  (selectedB : B -> Prop)
  (R : A -> B -> Prop)
  (hstep : forall {a b}, R a b -> Not (selectedA a) -> Not (selectedB b) -> R (sigma a) (tau b))
  (hfirst : R (sigma x.1) (tau y.1))
  (hnpos : 0 < n)
  (hnA : n <= finiteFirstReturnTime sigma selectedA x)
  (hnB : n <= finiteFirstReturnTime tau selectedB y) :
-- imply
  R ((sigma ^ n) x.1) ((tau ^ n) y.1) := by
-- proof
  apply StatMech.FrontierD.finiteRelated_until_firstReturn sigma tau selectedA selectedB R hstep x y hfirst n hnpos hnA hnB

/--
[finiteFirstReturnTime_eq_of_aligned_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturnTime_eq_of_aligned_first_eq
  [Fintype A]
  [DecidableEq A]
  [Fintype B]
  [DecidableEq B]
  {sigma : Equiv.Perm A}
  {tau : Equiv.Perm B}
  [DecidablePred selectedA]
  [DecidablePred selectedB]
  {x : {a : A // selectedA a}}
  {y : {b : B // selectedB b}}
-- given
  (selectedA : A -> Prop)
  (selectedB : B -> Prop)
  (R : A -> B -> Prop)
  (hselected : forall {a b}, R a b -> (selectedA a <-> selectedB b))
  (hstep : forall {a b}, R a b -> Not (selectedA a) -> Not (selectedB b) -> R (sigma a) (tau b))
  (hfirst : R (sigma x.1) (tau y.1)) :
-- imply
  finiteFirstReturnTime sigma selectedA x = finiteFirstReturnTime tau selectedB y := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturnTime_eq_of_aligned_first sigma tau selectedA selectedB R hselected hstep x y hfirst

/--
[finiteFirstReturn_related_of_aligned_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturn_related_of_aligned_first_eq
  [Fintype A]
  [DecidableEq A]
  [Fintype B]
  [DecidableEq B]
  {sigma : Equiv.Perm A}
  {tau : Equiv.Perm B}
  [DecidablePred selectedA]
  [DecidablePred selectedB]
  {x : {a : A // selectedA a}}
  {y : {b : B // selectedB b}}
-- given
  (selectedA : A -> Prop)
  (selectedB : B -> Prop)
  (R : A -> B -> Prop)
  (hselected : forall {a b}, R a b -> (selectedA a <-> selectedB b))
  (hstep : forall {a b}, R a b -> Not (selectedA a) -> Not (selectedB b) -> R (sigma a) (tau b))
  (hfirst : R (sigma x.1) (tau y.1)) :
-- imply
  R (finiteFirstReturn sigma selectedA x).1 (finiteFirstReturn tau selectedB y).1 := by
-- proof
  apply StatMech.FrontierD.finiteFirstReturn_related_of_aligned_first sigma tau selectedA selectedB R hselected hstep x y hfirst


-- created on 2026-10-23
