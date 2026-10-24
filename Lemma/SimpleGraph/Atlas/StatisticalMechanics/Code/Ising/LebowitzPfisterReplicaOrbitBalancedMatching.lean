import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching
open Finset StatMech StatMech.Ising


/--
[lpReplicaProfileOrbitLabelReallocates_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitLabelReallocates_all_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {M : LPReplicaProfileOrbitLabel G sites q n}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaProfileOrbitLabelReallocates G sites q L M := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitLabelReallocates_all G sites q L M

/--
[lpReplicaDecoratedOrbitAtomOfRowGate_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomOfRowGate_profile_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  (lpReplicaDecoratedOrbitAtomOfRowGate G sites m q tag A B hm hgate L).1.1.1 = m := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomOfRowGate_profile G sites m q tag A B hm hgate L

/--
[lpReplicaDecoratedOrbitAtomOfRowGate_orbitLabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomOfRowGate_orbitLabel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  (lpReplicaDecoratedOrbitAtomOfRowGate G sites m q tag A B hm hgate L).2.2 = L := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomOfRowGate_orbitLabel G sites m q tag A B hm hgate L

/--
[lpReplicaDecoratedOrbitAtomOfRowGate_row0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomOfRowGate_row0_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  (lpReplicaDecoratedOrbitAtomOfRowGate G sites m q tag A B hm hgate L).2.1.1 = lpReplicaRowCopies G sites m tag false := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomOfRowGate_row0 G sites m q tag A B hm hgate L

/--
[lpReplicaDecoratedOrbitAtom_cast_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtom_cast_profile_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A D E : Finset (LPReplicaCurrentVertex V)}
  {x : LPReplicaDecoratedOrbitAtom G sites A D q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (h : D = E) :
-- imply
  (cast (congrArg (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) h) x).1.1.1 = x.1.1.1 := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtom_cast_profile G sites A D E q h x

/--
[lpReplicaDecoratedOrbitAtom_cast_orbitLabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtom_cast_orbitLabel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A D E : Finset (LPReplicaCurrentVertex V)}
  {x : LPReplicaDecoratedOrbitAtom G sites A D q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (h : D = E) :
-- imply
  HEq (cast (congrArg (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) h) x).2.2 x.2.2 := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtom_cast_orbitLabel G sites A D E q h x

/--
[lpReplicaDecoratedOrbitAtom_cast_row0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtom_cast_row0_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A D E : Finset (LPReplicaCurrentVertex V)}
  {x : LPReplicaDecoratedOrbitAtom G sites A D q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (h : D = E) :
-- imply
  HEq (cast (congrArg (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) h) x).2.1.1 x.2.1.1 := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtom_cast_row0 G sites A D E q h x

/--
[lpReplicaDecoratedOrbitAtomOfBalancedSelector_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomOfBalancedSelector_profile_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {Si Sj T : Finset (LPReplicaCurrentVertex V)}
  {s : LPReplicaBalancedSelector G sites (Si ∆ Sj ∆ T) (Sj ∆ T) q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaDecoratedOrbitAtomOfBalancedSelector G sites Si Sj T q s).1.1.1 = s.profile := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomOfBalancedSelector_profile G sites Si Sj T q s

/--
[lpReplicaDecoratedOrbitAtomOfBalancedSelector_orbitLabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomOfBalancedSelector_orbitLabel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {Si Sj T : Finset (LPReplicaCurrentVertex V)}
  {s : LPReplicaBalancedSelector G sites (Si ∆ Sj ∆ T) (Sj ∆ T) q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaDecoratedOrbitAtomOfBalancedSelector G sites Si Sj T q s).2.2 = s.orbitLabel := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomOfBalancedSelector_orbitLabel G sites Si Sj T q s

/--
[lpReplicaDecoratedOrbitAtomOfBalancedSelector_row0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomOfBalancedSelector_row0_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {Si Sj T : Finset (LPReplicaCurrentVertex V)}
  {s : LPReplicaBalancedSelector G sites (Si ∆ Sj ∆ T) (Sj ∆ T) q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaDecoratedOrbitAtomOfBalancedSelector G sites Si Sj T q s).2.1.1 = lpReplicaRowCopies G sites s.profile (lpReplicaToggleRows G sites s.profile s.selector s.tag) false := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomOfBalancedSelector_row0 G sites Si Sj T q s

/--
[lpReplicaOffdiagBalancedMatch_iff_output](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedMatch_iff_output_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {y : LPReplicaOffdiagDecoratedTarget G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaOffdiagBalancedMatch G sites i j q z y ↔ LPReplicaOffdiagBalancedOutput G sites i j q y := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedMatch_iff_output G sites i j q z y

/--
[lpReplicaOffdiagDecoratedSource_card_eq_sum_profileFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_card_eq_sum_profileFibers_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) = ∑ m ∈ lpReplicaOffdiagBalancedRelevantProfiles G sites i j q, (lpReplicaOffdiagDecoratedSourcesAtProfile G sites i j q m).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_card_eq_sum_profileFibers G sites i j q

/--
[lpReplicaOffdiagBalancedLeftOutputs_card_eq_sum_profileFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedLeftOutputs_card_eq_sum_profileFibers_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaOffdiagBalancedLeftOutputs G sites i j q).card = ∑ m ∈ lpReplicaOffdiagBalancedRelevantProfiles G sites i j q, (lpReplicaOffdiagBalancedLeftOutputsAtProfile G sites i j q m).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedLeftOutputs_card_eq_sum_profileFibers G sites i j q

/--
[lpReplicaOffdiagBalancedRightOutputs_card_eq_sum_profileFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedRightOutputs_card_eq_sum_profileFibers_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaOffdiagBalancedRightOutputs G sites i j q).card = ∑ m ∈ lpReplicaOffdiagBalancedRelevantProfiles G sites i j q, (lpReplicaOffdiagBalancedRightOutputsAtProfile G sites i j q m).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedRightOutputs_card_eq_sum_profileFibers G sites i j q

/--
[lpReplicaOffdiagBalancedOutputs_eq_branch_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedOutputs_eq_branch_union_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaOffdiagBalancedOutputs G sites i j q = lpReplicaOffdiagBalancedBranchOutputs G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedOutputs_eq_branch_union G sites i j q

/--
[lpReplicaOffdiagBalancedBranchOutputs_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedBranchOutputs_disjoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Disjoint (lpReplicaOffdiagBalancedLeftOutputs G sites i j q) (lpReplicaOffdiagBalancedRightOutputs G sites i j q) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedBranchOutputs_disjoint G sites i j q

/--
[lpReplicaOffdiagBalancedOutputs_card_eq_branch_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedOutputs_card_eq_branch_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaOffdiagBalancedOutputs G sites i j q).card = (lpReplicaOffdiagBalancedLeftOutputs G sites i j q).card + (lpReplicaOffdiagBalancedRightOutputs G sites i j q).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedOutputs_card_eq_branch_sum G sites i j q

/--
[lpReplicaOffdiagDecoratedOrbitInjection_of_balancedHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedOrbitInjection_of_balancedHall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hHall : LPReplicaOffdiagBalancedHall G sites i j q) :
-- imply
  LPReplicaOffdiagDecoratedOrbitInjection G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedOrbitInjection_of_balancedHall G sites i j q hHall

/--
[lpReplicaOffdiagBalancedHall_of_outputCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedHall_of_outputCard_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <= (lpReplicaOffdiagBalancedOutputs G sites i j q).card) :
-- imply
  LPReplicaOffdiagBalancedHall G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedHall_of_outputCard G sites i j q hcard

/--
[lpReplicaOffdiagOrbitAtomCardInequality_of_balancedOutputCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_of_balancedOutputCard_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <= (lpReplicaOffdiagBalancedOutputs G sites i j q).card) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_of_balancedOutputCard G sites i j q hcard

/--
[lpReplicaOffdiagOrbitAtomCardInequality_of_balancedBranchOutputCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_of_balancedBranchOutputCard_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <= (lpReplicaOffdiagBalancedLeftOutputs G sites i j q).card + (lpReplicaOffdiagBalancedRightOutputs G sites i j q).card) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_of_balancedBranchOutputCard G sites i j q hcard

/--
[lpReplicaOffdiagOrbitAtomCardInequality_of_balancedProfileFiberCards](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_of_balancedProfileFiberCards_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : ∀ m ∈ lpReplicaOffdiagBalancedRelevantProfiles G sites i j q, (lpReplicaOffdiagDecoratedSourcesAtProfile G sites i j q m).card <= (lpReplicaOffdiagBalancedLeftOutputsAtProfile G sites i j q m).card + (lpReplicaOffdiagBalancedRightOutputsAtProfile G sites i j q m).card) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_of_balancedProfileFiberCards G sites i j q hcard


-- created on 2026-10-23
