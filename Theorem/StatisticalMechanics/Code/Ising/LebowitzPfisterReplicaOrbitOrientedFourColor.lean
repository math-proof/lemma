/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitOrientedFourColor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSplitTag.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor
open Finset


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaTagFourColor_colorClass_zero
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    colorClass Finset.univ (lpReplicaTagFourColor G sites m tag) 0 =
      lpReplicaCurrentCopies G sites m tag false false := by
  classical
  ext c
  rcases htag : tag c with ⟨r, current⟩
  cases r <;> cases current <;>
    simp [colorClass, lpReplicaTagFourColor, lpReplicaRowTagEquivFin4,
      lpReplicaCurrentCopies, htag]

theorem lpReplicaTagFourColor_colorClass_one
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    colorClass Finset.univ (lpReplicaTagFourColor G sites m tag) 1 =
      lpReplicaCurrentCopies G sites m tag false true := by
  classical
  ext c
  rcases htag : tag c with ⟨r, current⟩
  cases r <;> cases current <;>
    simp [colorClass, lpReplicaTagFourColor, lpReplicaRowTagEquivFin4,
      lpReplicaCurrentCopies, htag]

theorem lpReplicaTagFourColor_colorClass_two
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    colorClass Finset.univ (lpReplicaTagFourColor G sites m tag) 2 =
      lpReplicaCurrentCopies G sites m tag true false := by
  classical
  ext c
  rcases htag : tag c with ⟨r, current⟩
  cases r <;> cases current <;>
    simp [colorClass, lpReplicaTagFourColor, lpReplicaRowTagEquivFin4,
      lpReplicaCurrentCopies, htag]

theorem lpReplicaTagFourColor_colorClass_three
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    colorClass Finset.univ (lpReplicaTagFourColor G sites m tag) 3 =
      lpReplicaCurrentCopies G sites m tag true true := by
  classical
  ext c
  rcases htag : tag c with ⟨r, current⟩
  cases r <;> cases current <;>
    simp [colorClass, lpReplicaTagFourColor, lpReplicaRowTagEquivFin4,
      lpReplicaCurrentCopies, htag]

theorem lpReplicaTagFourColor_rowClass_zero
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    rowClass Finset.univ (lpReplicaTagFourColor G sites m tag) 0 =
      lpReplicaRowCopies G sites m tag false := by
  classical
  ext c
  rcases htag : tag c with ⟨r, current⟩
  cases r <;> cases current <;>
    simp [rowClass, colorClass, lpReplicaTagFourColor,
      lpReplicaRowTagEquivFin4, lpReplicaRowCopies, htag]

theorem lpReplicaTagFourColor_rowClass_one
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    rowClass Finset.univ (lpReplicaTagFourColor G sites m tag) 1 =
      lpReplicaRowCopies G sites m tag true := by
  classical
  ext c
  rcases htag : tag c with ⟨r, current⟩
  cases r <;> cases current <;>
    simp [rowClass, colorClass, lpReplicaTagFourColor,
      lpReplicaRowTagEquivFin4, lpReplicaRowCopies, htag]


theorem lpReplicaRowGate_iff_leftPattern_tagFourColor
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    LPReplicaRowGate G sites m A B tag ↔
      LeftPattern (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ
        A B lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
        (lpReplicaTagFourColor G sites m tag) := by
  unfold LPReplicaRowGate LeftPattern RowsDisconnect
  rw [lpReplicaTagFourColor_colorClass_zero,
    lpReplicaTagFourColor_colorClass_one,
    lpReplicaTagFourColor_colorClass_two,
    lpReplicaTagFourColor_colorClass_three,
    lpReplicaTagFourColor_rowClass_zero,
    lpReplicaTagFourColor_rowClass_one]
  constructor
  · rintro ⟨h0, h1, hd0, h2, h3, hd1⟩
    exact ⟨h0, h1, h2, h3, hd0, hd1⟩
  · rintro ⟨h0, h1, h2, h3, hd0, hd1⟩
    exact ⟨h0, h1, hd0, h2, h3, hd1⟩


end
end StatMech.Ising
