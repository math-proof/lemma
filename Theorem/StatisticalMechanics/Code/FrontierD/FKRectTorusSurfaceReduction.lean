/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSurfaceReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingRankTwoInsertion
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSurfaceReduction
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectConnectedInsertionSurfaceBridge_iff_defectJump_iff_hasNet
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F)) :
    FKRectConnectedInsertionSurfaceBridge R F e r heF hold ↔
      (fkRectEulerHomologyDefect R
          (fkRectConfigurationOfEdges R (insert e F)) =
          fkRectEulerHomologyDefect R
            (fkRectConfigurationOfEdges R F) + 2 ↔
        FKRectHasNet R
          (fkRectConfigurationOfEdges R (insert e F))) := by
  rw [fkRectEulerHomologyDefect_insert_eq_add_two_iff R F e heF,
    fkRectHasNet_insert_iff_exists_independent_fundamentalWalk
      R F e r hold]
  have hreach : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e) :=
    ⟨r⟩
  simp only [hreach, true_and]
  rfl


theorem fkRectEulerHomologyDefect_insert_eq_add_two_iff_hasNet
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F))
    (hsurface : FKRectConnectedInsertionSurfaceBridge R F e r heF hold) :
    fkRectEulerHomologyDefect R
        (fkRectConfigurationOfEdges R (insert e F)) =
        fkRectEulerHomologyDefect R
          (fkRectConfigurationOfEdges R F) + 2 ↔
      FKRectHasNet R
        (fkRectConfigurationOfEdges R (insert e F)) := by
  rw [fkRectEulerHomologyDefect_insert_eq_add_two_iff R F e heF]
  rw [fkRectHasNet_insert_iff_exists_independent_fundamentalWalk
    R F e r hold]
  constructor
  · rintro ⟨-, hmedial⟩
    exact hsurface.mp hmedial
  · intro hind
    exact ⟨⟨r⟩, hsurface.mpr hind⟩


theorem fkRectEulerHomologyDefect_insert_eq_two_iff_hasNet
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (hzero : fkRectEulerHomologyDefect R
      (fkRectConfigurationOfEdges R F) = 0)
    (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F))
    (hsurface : FKRectConnectedInsertionSurfaceBridge R F e r heF hold) :
    fkRectEulerHomologyDefect R
        (fkRectConfigurationOfEdges R (insert e F)) = 2 ↔
      FKRectHasNet R
        (fkRectConfigurationOfEdges R (insert e F)) := by
  have h := fkRectEulerHomologyDefect_insert_eq_add_two_iff_hasNet
    R F e heF r hold hsurface
  rwa [hzero, zero_add] at h

end
end StatMech.FrontierD
