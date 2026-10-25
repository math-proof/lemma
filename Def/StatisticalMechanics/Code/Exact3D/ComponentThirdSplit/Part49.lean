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
import Structure.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part3
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in

def SourceClassEndpointMembershipResidualShellShare15.fourShare
    {n : ℕ} {v : FK.boxVerts 3 n}
    (Sh : SourceClassEndpointMembershipResidualShellShare15 v)
    (hasGhost hasOrigin hasEndpoint : Bool) : ℕ → ℝ :=
  match hasGhost, hasOrigin, hasEndpoint with
  | false, false, false => Sh.four_none
  | false, false, true => Sh.four_endpoint
  | false, true, false => Sh.four_origin
  | false, true, true => Sh.four_origin_endpoint
  | true, false, false => Sh.four_ghost
  | true, false, true => Sh.four_ghost_endpoint
  | true, true, false => Sh.four_ghost_origin
  | true, true, true => Sh.four_ghost_origin_endpoint

set_option linter.style.longLine false in


def SourceClassEndpointMembershipResidualShellShare15.ofFourShare
    {n : ℕ} (v : FK.boxVerts 3 n)
    (zero_none two_none two_endpoint two_origin two_ghost
      two_ghost_endpoint two_ghost_origin : ℝ)
    (fourShare : Bool → Bool → Bool → ℕ → ℝ) :
    SourceClassEndpointMembershipResidualShellShare15 v where
  zero_none := zero_none
  two_none := two_none
  two_endpoint := two_endpoint
  two_origin := two_origin
  two_ghost := two_ghost
  two_ghost_endpoint := two_ghost_endpoint
  two_ghost_origin := two_ghost_origin
  four_none := fourShare false false false
  four_endpoint := fourShare false false true
  four_origin := fourShare false true false
  four_origin_endpoint := fourShare false true true
  four_ghost := fourShare true false false
  four_ghost_endpoint := fourShare true false true
  four_ghost_origin := fourShare true true false
  four_ghost_origin_endpoint := fourShare true true true

end Exact3D
end StatMech
