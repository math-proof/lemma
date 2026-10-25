/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialBoundaryWalk.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundary.Part3


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRefinedBoundaryDarts_path {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T)
    (c : Int × Int) (n : Nat) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedDartPoint c d.2)
      (fkRectRefinedDartPoint
        (fkRectRefinedBoundaryCenterAfter pairing d c n)
        (((fkMedialBoundaryStep pairing)^[n] d).2))
      (fkRectRefinedBoundaryDarts pairing d c n) := by
  induction n generalizing d c with
  | zero =>
      exact FKRectIntegralSquareDartPath.nil _
  | succ n ih =>
      let localSide := (fkMedialLocalMate pairing d).2
      let next := fkMedialBoundaryStep pairing d
      let nextCenter := fkRectRefinedBondCenter c localSide
      have hlocal : FKRectIntegralSquareDartPath
          (fkRectRefinedDartPoint c d.2)
          (fkRectRefinedDartPoint c localSide)
          (fkRectRefinedLocalDarts (pairing d.1) c d.2) := by
        simpa [localSide, fkMedialLocalMate_side] using
          fkRectRefinedLocalDarts_path (pairing d.1) c d.2
      have htail := ih next nextCenter
      have hbond : fkRectRefinedDartPoint nextCenter next.2 =
          fkRectRefinedDartPoint c localSide := by
        simpa [next, nextCenter, localSide] using
          fkRectRefinedDartPoint_bondMate T c
            (fkMedialLocalMate pairing d)
      rw [hbond] at htail
      have happend := hlocal.append htail
      simpa [fkRectRefinedBoundaryDarts,
        fkRectRefinedBoundaryCenterAfter, next, nextCenter, localSide,
        Function.iterate_succ_apply] using happend


theorem fkRectRefinedBoundaryOrbitDarts_path {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T)
    (c : Int × Int) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedDartPoint c d.2)
      (fkRectRefinedDartPoint
        (fkRectRefinedBoundaryCenterAfter pairing d c
          (orderOf (fkMedialBoundaryStep pairing))) d.2)
      (fkRectRefinedBoundaryDarts pairing d c
        (orderOf (fkMedialBoundaryStep pairing))) := by
  have h := fkRectRefinedBoundaryDarts_path pairing d c
    (orderOf (fkMedialBoundaryStep pairing))
  have hpow : (fkMedialBoundaryStep pairing) ^
      orderOf (fkMedialBoundaryStep pairing) = 1 :=
    pow_orderOf_eq_one _
  have hreturn :
      (fkMedialBoundaryStep pairing)^[orderOf
          (fkMedialBoundaryStep pairing)] d = d := by
    rw [← Equiv.Perm.coe_pow]
    simpa only [hpow, Equiv.Perm.one_apply]
  rwa [hreturn] at h


theorem fkRectCanonicalSquareEdgeStep_eq
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).2 -
        fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1 =
      if fkRectClosedPairingAtEdge e then (-1, 0) else (0, 1) := by
  rcases e with ⟨b, x, y⟩
  cases b <;> by_cases hy : Even y.val
  all_goals
    simp [fkRectLiftedIndexedEdgeEnds, fkRectClosedPairingAtEdge,
      fkRectSquareDevelopPoint, hy]
  · obtain ⟨k, hk⟩ := hy
    omega
  · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hy
    omega
  · obtain ⟨k, hk⟩ := hy
    omega
  · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hy
    omega


theorem fkRectLiftedIndexedEdgeEnds_medialPrimal_orientation
    (R : FKRectTorus) (e : R.EdgeIndex) :
    if fkRectClosedPairingAtEdge e then
      fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).1 =
          fkRectMedialEastPrimal R e ∧
        fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).2 =
          fkRectMedialWestPrimal R e
    else
      fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).1 =
          fkRectMedialWestPrimal R e ∧
        fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).2 =
          fkRectMedialEastPrimal R e := by
  rcases e with ⟨b, x, y⟩
  cases b <;> by_cases hy : Even y.val <;>
    simp [fkRectLiftedIndexedEdgeEnds, fkRectLiftedVertex,
      fkRectMedialEastPrimal, fkRectMedialWestPrimal,
      fkRectClosedPairingAtEdge, hy]


end
end StatMech.FrontierD
