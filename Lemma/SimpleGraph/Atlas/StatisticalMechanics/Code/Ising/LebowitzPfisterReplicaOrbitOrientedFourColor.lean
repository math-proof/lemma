import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
open Finset StatMech StatMech.Ising


/--
[lpReplicaTagFourColor_colorClass_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitOrientedFourColor.lean)
-/
@[path]
private lemma lpReplicaTagFourColor_colorClass_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  colorClass Finset.univ (lpReplicaTagFourColor G sites m tag) 0 = lpReplicaCurrentCopies G sites m tag false false := by
-- proof
  apply StatMech.Ising.lpReplicaTagFourColor_colorClass_zero G sites m tag

/--
[lpReplicaTagFourColor_colorClass_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitOrientedFourColor.lean)
-/
@[path]
private lemma lpReplicaTagFourColor_colorClass_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  colorClass Finset.univ (lpReplicaTagFourColor G sites m tag) 1 = lpReplicaCurrentCopies G sites m tag false true := by
-- proof
  apply StatMech.Ising.lpReplicaTagFourColor_colorClass_one G sites m tag

/--
[lpReplicaTagFourColor_colorClass_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitOrientedFourColor.lean)
-/
@[path]
private lemma lpReplicaTagFourColor_colorClass_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  colorClass Finset.univ (lpReplicaTagFourColor G sites m tag) 2 = lpReplicaCurrentCopies G sites m tag true false := by
-- proof
  apply StatMech.Ising.lpReplicaTagFourColor_colorClass_two G sites m tag

/--
[lpReplicaTagFourColor_colorClass_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitOrientedFourColor.lean)
-/
@[path]
private lemma lpReplicaTagFourColor_colorClass_three_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  colorClass Finset.univ (lpReplicaTagFourColor G sites m tag) 3 = lpReplicaCurrentCopies G sites m tag true true := by
-- proof
  apply StatMech.Ising.lpReplicaTagFourColor_colorClass_three G sites m tag

/--
[lpReplicaTagFourColor_rowClass_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitOrientedFourColor.lean)
-/
@[path]
private lemma lpReplicaTagFourColor_rowClass_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  rowClass Finset.univ (lpReplicaTagFourColor G sites m tag) 0 = lpReplicaRowCopies G sites m tag false := by
-- proof
  apply StatMech.Ising.lpReplicaTagFourColor_rowClass_zero G sites m tag

/--
[lpReplicaTagFourColor_rowClass_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitOrientedFourColor.lean)
-/
@[path]
private lemma lpReplicaTagFourColor_rowClass_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  rowClass Finset.univ (lpReplicaTagFourColor G sites m tag) 1 = lpReplicaRowCopies G sites m tag true := by
-- proof
  apply StatMech.Ising.lpReplicaTagFourColor_rowClass_one G sites m tag

/--
[lpReplicaRowGate_iff_leftPattern_tagFourColor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitOrientedFourColor.lean)
-/
@[path]
private lemma lpReplicaRowGate_iff_leftPattern_tagFourColor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  LPReplicaRowGate G sites m A B tag ↔ LeftPattern (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ A B lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (lpReplicaTagFourColor G sites m tag) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_iff_leftPattern_tagFourColor G sites m A B tag

/--
[card_lpReplicaOrientedFourColorFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitOrientedFourColor.lean)
-/
@[path]
private lemma card_lpReplicaOrientedFourColorFiber_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (m : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // lpReplicaSymmetrizedProfile G sites p = q}) :
-- imply
  Fintype.card (LPReplicaOrientedFourColorFiber G sites A B q m) = ∑ a : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // p <= m.1}, lpReplicaCollisionSplitMultiplicity G sites m.1 a.1 * lpReplicaProfileOrbitMultiplicity G sites q m.1 * (lpReplicaDisconnProfileFamily G sites A a.1).card * (lpReplicaDisconnProfileFamily G sites B (lpReplicaReflectedResidual G sites m.1 a.1)).card := by
-- proof
  apply StatMech.Ising.card_lpReplicaOrientedFourColorFiber G sites A B q m

/--
[card_lpReplicaOrientedFourColorAtom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitOrientedFourColor.lean)
-/
@[path]
private lemma card_lpReplicaOrientedFourColorAtom_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaOrientedFourColorAtom G sites A B q) = Fintype.card (LPReplicaDecoratedOrbitAtom G sites A B q) := by
-- proof
  apply StatMech.Ising.card_lpReplicaOrientedFourColorAtom G sites A B q

/--
[lpReplicaOrientedFourColorTag_leftPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitOrientedFourColor.lean)
-/
@[path]
private lemma lpReplicaOrientedFourColorTag_leftPattern_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {z : LPReplicaOrientedFourColorAtom G sites A B q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LeftPattern (endsM (lpReplicaCurrentGraph G sites) z.1.1) Finset.univ A (B.map lpReplicaCurrentReflect.toEmbedding) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (lpReplicaTagFourColor G sites z.1.1 (lpReplicaOrientedFourColorTag G sites A B q z)) := by
-- proof
  apply StatMech.Ising.lpReplicaOrientedFourColorTag_leftPattern G sites A B q z


-- created on 2026-10-23
