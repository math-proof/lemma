/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part7
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

noncomputable def triHexTorusDualConfig (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (TorusSite L))) :
    ConfigSpace (Sym2 (HexTorusVertex L)) := fun e =>
  if _ : e ∈ (hexagonalTorusGraph L).edgeSet then
    !(omega (triHexTorusPrimalOfDualEdge L e))
  else false


end PeriodicPlanar
end FK
end StatMech
