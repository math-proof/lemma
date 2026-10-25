/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Hall.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaSameProfileCounterexample.Part2
import Abbrev.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaDecoratedOrbitAtomOfRowGate_profile
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    (lpReplicaDecoratedOrbitAtomOfRowGate
      G sites m q tag A B hm hgate L).1.1.1 = m := rfl

@[simp] theorem lpReplicaDecoratedOrbitAtomOfRowGate_orbitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    (lpReplicaDecoratedOrbitAtomOfRowGate
      G sites m q tag A B hm hgate L).2.2 = L := rfl

@[simp] theorem lpReplicaDecoratedOrbitAtomOfRowGate_row0
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    (lpReplicaDecoratedOrbitAtomOfRowGate
      G sites m q tag A B hm hgate L).2.1.1 =
        lpReplicaRowCopies G sites m tag false := rfl

theorem lpReplicaDecoratedOrbitAtom_cast_profile
    (G : SimpleGraph V) (sites : I -> V)
    (A D E : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (h : D = E) (x : LPReplicaDecoratedOrbitAtom G sites A D q) :
    (cast (congrArg
      (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) h) x).1.1.1 =
        x.1.1.1 := by
  subst E
  rfl

theorem lpReplicaDecoratedOrbitAtom_cast_orbitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (A D E : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (h : D = E) (x : LPReplicaDecoratedOrbitAtom G sites A D q) :
    HEq (cast (congrArg
      (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) h) x).2.2
      x.2.2 := by
  subst E
  rfl

theorem lpReplicaDecoratedOrbitAtom_cast_row0
    (G : SimpleGraph V) (sites : I -> V)
    (A D E : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (h : D = E) (x : LPReplicaDecoratedOrbitAtom G sites A D q) :
    HEq (cast (congrArg
      (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) h) x).2.1.1
      x.2.1.1 := by
  subst E
  rfl

@[simp] theorem lpReplicaDecoratedOrbitAtomOfBalancedSelector_profile
    (G : SimpleGraph V) (sites : I -> V)
    (Si Sj T : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q) :
    (lpReplicaDecoratedOrbitAtomOfBalancedSelector
      G sites Si Sj T q s).1.1.1 = s.profile := rfl

@[simp] theorem lpReplicaDecoratedOrbitAtomOfBalancedSelector_orbitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (Si Sj T : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q) :
    (lpReplicaDecoratedOrbitAtomOfBalancedSelector
      G sites Si Sj T q s).2.2 = s.orbitLabel := rfl

@[simp] theorem lpReplicaDecoratedOrbitAtomOfBalancedSelector_row0
    (G : SimpleGraph V) (sites : I -> V)
    (Si Sj T : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q) :
    (lpReplicaDecoratedOrbitAtomOfBalancedSelector
      G sites Si Sj T q s).2.1.1 =
      lpReplicaRowCopies G sites s.profile
        (lpReplicaToggleRows G sites s.profile s.selector s.tag) false := rfl


end
end StatMech.Ising
