import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove
open Finset StatMech StatMech.Ising


/--
[lpReplicaOrbitCommonSlotsOfCopies_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitExactTagSlotMove.lean)
-/
@[path]
private lemma lpReplicaOrbitCommonSlotsOfCopies_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  Function.Injective (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCommonSlotsOfCopies_injective G sites q m hm L

/--
[lpReplicaOrbitFourColorSlotRowMask_stateOfTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitExactTagSlotMove.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotRowMask_stateOfTag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) = lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L (lpReplicaRowCopies G sites m tag true) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotRowMask_stateOfTag G sites q m hm L tag

/--
[lpReplicaOrbitFourColorSlotCrossToggle_left_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitExactTagSlotMove.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotCrossToggle_left_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Injective fun P => lpReplicaOrbitFourColorSlotCrossToggle G sites q P s := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotCrossToggle_left_injective G sites q s

/--
[lpReplicaOrbitFourColorSlotEdge_crossToggle_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitExactTagSlotMove.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotEdge_crossToggle_of_not_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
  {x : LPReplicaOrbitCommonSlot G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hx : x ∉ P) :
-- imply
  lpReplicaOrbitFourColorSlotEdge G sites q (lpReplicaOrbitFourColorSlotCrossToggle G sites q P s) x = lpReplicaOrbitFourColorSlotEdge G sites q s x := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotEdge_crossToggle_of_not_mem G sites q P s x hx

/--
[lpReplicaOrbitFourColorSlotEdge_crossToggle_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitExactTagSlotMove.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotEdge_crossToggle_of_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
  {x : LPReplicaOrbitCommonSlot G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hx : x ∈ P) :
-- imply
  lpReplicaOrbitFourColorSlotEdge G sites q (lpReplicaOrbitFourColorSlotCrossToggle G sites q P s) x = lpReplicaCurrentEdgeReflect G sites (lpReplicaOrbitFourColorSlotEdge G sites q s x) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotEdge_crossToggle_of_mem G sites q P s x hx

/--
[lpReplicaOffdiagDecoratedTarget_ne_of_singletonCrossToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitExactTagSlotMove.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedTarget_ne_of_singletonCrossToggle_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {y w : LPReplicaOffdiagDecoratedTarget G sites i j q}
  {c e : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hy : (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 {c}) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z))
  (hw : (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q w).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 {e}) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z))
  (hce : c ≠ e) :
-- imply
  y ≠ w := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedTarget_ne_of_singletonCrossToggle G sites i j q z y w c e hy hw hce

/--
[lpReplicaBalancedSelector_slotState_of_singletonToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitExactTagSlotMove.lean)
-/
@[path]
private lemma lpReplicaBalancedSelector_slotState_of_singletonToggle_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {Si Sj T : Finset (LPReplicaCurrentVertex V)}
  {s : LPReplicaBalancedSelector G sites (Si ∆ Sj ∆ T) (Sj ∆ T) q}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) s.profile}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (sourceTag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) s.profile -> LPReplicaRowTag)
  (hmove : lpReplicaToggleRows G sites s.profile s.selector s.tag = lpReplicaToggleRows G sites s.profile {c} sourceTag)
  (hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites) :
-- imply
  lpReplicaOrientedFourColorSlotState G sites Si ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites Si ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q (lpReplicaDecoratedOrbitAtomOfBalancedSelector G sites Si Sj T q s)) = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q s.profile s.orbit s.orbitLabel {c}) (lpReplicaOrbitFourColorSlotStateOfTag G sites q s.profile s.orbit s.orbitLabel sourceTag) := by
-- proof
  apply StatMech.Ising.lpReplicaBalancedSelector_slotState_of_singletonToggle G sites Si Sj T q s c sourceTag hmove hfixed


-- created on 2026-10-23
