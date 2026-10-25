/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable instance instFintypeCanonicalStableRawExceptionalEdge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I) :
    Fintype (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) := by
  classical
  let T : Type _ := ↑(canonicalRawCommonClosure ends m j k l zero p)
  let U : Type _ := ↑(StatMech.FrontierA.finiteRelationNeighborhood
    (CanonicalRawGateRelated ends m j k l zero p)
    (canonicalRawCommonClosure ends m j k l zero p))
  let E : Type _ := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let f : E → T × U := fun s => (s.source, s.target)
  letI : Finite E := Finite.of_injective f (by
    intro s t h
    cases s
    cases t
    simp only [f, Prod.mk.injEq] at h
    simp_all)
  exact Fintype.ofFinite E


end StatMech.GrahamGHS.FourColor
