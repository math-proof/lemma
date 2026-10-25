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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part37
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
    {n : ℕ} (v : FK.boxVerts 3 n)
    (β H : ℝ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (hasGhost hasOrigin hasEndpoint : Bool)
    (R : Finset (Option (FK.boxVerts 3 n)))
    (share D : ℝ) : Prop :=
  0 ≤ share ∧
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v
        (finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint ∪ R) ≤
      share * D

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSum
    {n : ℕ} (v : FK.boxVerts 3 n)
    (β H : ℝ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (hasGhost hasOrigin hasEndpoint : Bool)
    (R : Finset (Option (FK.boxVerts 3 n)))
    {ι : Type*} [DecidableEq ι]
    (label :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι)
    (i : ι) : ℝ :=
  ∑ E ∈
    ((finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
      n Ω v).filter
      (fun E =>
        E.1 =
          finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪ R)).filter
      (fun E => label E = i),
    finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
    {n : ℕ} (v : FK.boxVerts 3 n)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (hasGhost hasOrigin hasEndpoint : Bool)
    (R : Finset (Option (FK.boxVerts 3 n))) :
    Finset (finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v) :=
  (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
    n Ω v).filter
    (fun E =>
      E.1 =
        finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint ∪ R)

end Exact3D
end StatMech
