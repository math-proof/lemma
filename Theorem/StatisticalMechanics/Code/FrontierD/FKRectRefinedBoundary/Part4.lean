/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialBoundaryWalk.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundary.Part4


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRefinedFourWest_path (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1 - 4, p.2)
      [(p, 2), ((p.1 - 1, p.2), 2), ((p.1 - 2, p.2), 2),
        ((p.1 - 3, p.2), 2)] := by
  have h1 := fkRectRefinedTwoWest_path p
  have h2 := fkRectRefinedTwoWest_path (p.1 - 2, p.2)
  have h := h1.append h2
  convert h using 1 <;> simp <;> ring

theorem fkRectRefinedFourNorth_path (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1, p.2 + 4)
      [(p, 1), ((p.1, p.2 + 1), 1), ((p.1, p.2 + 2), 1),
        ((p.1, p.2 + 3), 1)] := by
  have h1 := fkRectRefinedTwoNorth_path p
  have h2 := fkRectRefinedTwoNorth_path (p.1, p.2 + 2)
  have h := h1.append h2
  convert h using 1 <;> simp <;> ring


theorem fkRectRefinedFourEast_path (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1 + 4, p.2)
      [(p, 0), ((p.1 + 1, p.2), 0), ((p.1 + 2, p.2), 0),
        ((p.1 + 3, p.2), 0)] := by
  have h1 := fkRectRefinedTwoEast_path p
  have h2 := fkRectRefinedTwoEast_path (p.1 + 2, p.2)
  have h := h1.append h2
  convert h using 1 <;> simp <;> ring


theorem fkRectRefinedFourWest_path_public (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1 - 4, p.2)
      [(p, 2), ((p.1 - 1, p.2), 2), ((p.1 - 2, p.2), 2),
        ((p.1 - 3, p.2), 2)] :=
  fkRectRefinedFourWest_path p


theorem fkRectRefinedFourNorth_path_public (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1, p.2 + 4)
      [(p, 1), ((p.1, p.2 + 1), 1), ((p.1, p.2 + 2), 1),
        ((p.1, p.2 + 3), 1)] :=
  fkRectRefinedFourNorth_path p


theorem fkRectRefinedFourSouth_path (p : Int × Int) :
    FKRectIntegralSquareDartPath p (p.1, p.2 - 4)
      [(p, 3), ((p.1, p.2 - 1), 3), ((p.1, p.2 - 2), 3),
        ((p.1, p.2 - 3), 3)] := by
  have h1 := fkRectRefinedTwoSouth_path p
  have h2 := fkRectRefinedTwoSouth_path (p.1, p.2 - 2)
  have h := h1.append h2
  convert h using 1 <;> simp <;> ring


theorem fkRectRefinedPrimalEdgeDarts_path
    (R : FKRectTorus) (e : R.EdgeIndex) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedPrimalEdgeStart R e)
      (fkRectRefinedPrimalEdgeEnd R e)
      (fkRectRefinedPrimalEdgeDarts R e) := by
  have hend : fkRectRefinedPrimalEdgeEnd R e =
      if fkRectClosedPairingAtEdge e then
        ((fkRectRefinedPrimalEdgeStart R e).1 - 4,
          (fkRectRefinedPrimalEdgeStart R e).2)
      else
        ((fkRectRefinedPrimalEdgeStart R e).1,
          (fkRectRefinedPrimalEdgeStart R e).2 + 4) := by
    have h := fkRectCanonicalSquareEdgeStep_eq R e
    by_cases hp : fkRectClosedPairingAtEdge e = true
    · simp [hp] at h ⊢
      unfold fkRectRefinedPrimalEdgeStart fkRectRefinedPrimalEdgeEnd
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at h1 h2
      apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega
    · have hp' : fkRectClosedPairingAtEdge e = false :=
        Bool.eq_false_of_not_eq_true hp
      simp [hp, hp'] at h ⊢
      unfold fkRectRefinedPrimalEdgeStart fkRectRefinedPrimalEdgeEnd
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst, Prod.snd] at h1 h2
      apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega
  rw [hend]
  by_cases hp : fkRectClosedPairingAtEdge e
  · simpa [fkRectRefinedPrimalEdgeDarts, hp] using
      fkRectRefinedFourWest_path (fkRectRefinedPrimalEdgeStart R e)
  · simpa [fkRectRefinedPrimalEdgeDarts, hp] using
      fkRectRefinedFourNorth_path (fkRectRefinedPrimalEdgeStart R e)

end
end StatMech.FrontierD
