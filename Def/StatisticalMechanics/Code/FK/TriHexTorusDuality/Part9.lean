/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part9
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

noncomputable def triHexTorusPrimalSectorSum
    (L : ℕ) [Fact (2 < L)] (r : ℤ) (p q : ℝ)
    (F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 (TorusSite L)),
    if triHexTorusDefect L
        (FK.openSub (triangularTorusGraph L) omega) = r then
      F (triHexTorusDualConfig L omega) *
        FK.fkWeight (triangularTorusGraph L) p q omega
    else 0


noncomputable def triHexTorusDualSectorSum
    (L : ℕ) [Fact (2 < L)] (r : ℤ) (pDual q : ℝ)
    (F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 (TorusSite L)),
    if triHexTorusDefect L
        (FK.openSub (triangularTorusGraph L) omega) = r then
      F (triHexTorusDualConfig L omega) *
        FK.fkWeight (hexagonalTorusGraph L) pDual q
          (triHexTorusDualConfig L omega)
    else 0


end PeriodicPlanar
end FK
end StatMech
