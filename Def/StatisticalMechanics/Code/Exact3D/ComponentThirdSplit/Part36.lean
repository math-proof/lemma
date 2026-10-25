/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part33
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (four_none four_endpoint four_origin four_origin_endpoint : ℝ)
    (four_ghost four_ghost_endpoint four_ghost_origin : ℝ)
    (four_ghost_origin_endpoint : ℝ) :
    SourceClassEndpointMembershipLiveBudget15 where
  zero_none :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
      β H n Ω v ∅
  two_none :=
    ∑ S ∈
      Finset.image₂
        (fun x y => ({x, y} : Finset (Option (FK.boxVerts 3 n))))
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v)
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S
  two_endpoint :=
    ∑ S ∈
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).image
        (fun x => ({some v, x} : Finset (Option (FK.boxVerts 3 n)))),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S
  two_origin :=
    ∑ S ∈
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).image
        (fun x =>
          ({some (IsingFK.boxOrigin 3 n), x} :
            Finset (Option (FK.boxVerts 3 n)))),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S
  two_ghost :=
    ∑ S ∈
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).image
        (fun x => ({none, x} : Finset (Option (FK.boxVerts 3 n)))),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S
  two_ghost_endpoint :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
      β H n Ω v ({none, some v} : Finset (Option (FK.boxVerts 3 n)))
  two_ghost_origin :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
      β H n Ω v
      ({none, some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n)))
  four_none := four_none
  four_endpoint := four_endpoint
  four_origin := four_origin
  four_origin_endpoint := four_origin_endpoint
  four_ghost := four_ghost
  four_ghost_endpoint := four_ghost_endpoint
  four_ghost_origin := four_ghost_origin
  four_ghost_origin_endpoint := four_ghost_origin_endpoint

set_option linter.style.longLine false in

noncomputable def finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualImageSourceClassSum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) : ℝ :=
  ∑ S ∈
    (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.image
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪ R),
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
      β H n Ω v S

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) : ℝ :=
  ∑ S ∈
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        4 ≤
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R).card)).image
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪ R),
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
      β H n Ω v S

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) : ℝ :=
  ∑ S ∈
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ R.card)).image
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪ R),
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
      β H n Ω v S

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) : Finset ℕ :=
  (Finset.range
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card + 1)).filter
    (fun k =>
      finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
        hasGhost hasOrigin hasEndpoint ≤ k)

end Exact3D
end StatMech
