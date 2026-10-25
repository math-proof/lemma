/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryOrbitVisits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryOrbitReachability
import Abbrev.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryOrbitVisits
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}


theorem fkMedial_west_east_visitCount_eq_zero_iff_not_reachable
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    fkMedialBoundaryOrbitVisitCount pairing
        (fkMedialWestDart v) (fkMedialEastDart v) = 0 ↔
      ¬ (fkMedialLoopGraph T pairing).Reachable
        (fkMedialWestDart v) (fkMedialEastDart v) := by
  rw [permOrbitVisitCount_eq_zero_iff_not_sameCycle,
    fkMedial_west_east_sameCycle_iff_reachable]


theorem fkMedial_west_visitCount_eq_east_visitCount_iff_reachable
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    fkMedialBoundaryOrbitVisitCount pairing
        (fkMedialWestDart v) (fkMedialWestDart v) =
      fkMedialBoundaryOrbitVisitCount pairing
        (fkMedialWestDart v) (fkMedialEastDart v) ↔
      (fkMedialLoopGraph T pairing).Reachable
        (fkMedialWestDart v) (fkMedialEastDart v) := by
  constructor
  · intro hcount
    by_contra hreach
    have heast : fkMedialBoundaryOrbitVisitCount pairing
        (fkMedialWestDart v) (fkMedialEastDart v) = 0 :=
      (fkMedial_west_east_visitCount_eq_zero_iff_not_reachable
        pairing v).2 hreach
    have hwest : 0 < fkMedialBoundaryOrbitVisitCount pairing
        (fkMedialWestDart v) (fkMedialWestDart v) :=
      (permOrbitVisitCount_pos_iff_sameCycle _ _ _).2 ⟨0, rfl⟩
    omega
  · intro hreach
    apply permOrbitVisitCount_eq_of_sameCycle
    exact (fkMedial_west_east_sameCycle_iff_reachable pairing v).2 hreach


theorem fkMedial_west_sub_east_visitCount_ne_zero_iff_not_reachable
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    ((fkMedialBoundaryOrbitVisitCount pairing
          (fkMedialWestDart v) (fkMedialWestDart v) : Int) -
        fkMedialBoundaryOrbitVisitCount pairing
          (fkMedialWestDart v) (fkMedialEastDart v) ≠ 0) ↔
      ¬ (fkMedialLoopGraph T pairing).Reachable
        (fkMedialWestDart v) (fkMedialEastDart v) := by
  constructor
  · intro hdiff hreach
    apply hdiff
    apply sub_eq_zero.mpr
    exact_mod_cast
      (fkMedial_west_visitCount_eq_east_visitCount_iff_reachable
        pairing v).2 hreach
  · intro hreach hzero
    apply hreach
    apply (fkMedial_west_visitCount_eq_east_visitCount_iff_reachable
      pairing v).1
    exact_mod_cast (sub_eq_zero.mp hzero)

end
end StatMech.FrontierD
