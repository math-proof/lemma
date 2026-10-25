/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDefectClassify.Part6
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

noncomputable def triHexTorusPrimalPartitionSum
    (L : ℕ) [Fact (2 < L)] (p q : ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 (TorusSite L)),
    FK.fkWeight (triangularTorusGraph L) p q omega


noncomputable def triHexTorusDualPartitionSum
    (L : ℕ) [Fact (2 < L)] (pDual q : ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 (TorusSite L)),
    FK.fkWeight (hexagonalTorusGraph L) pDual q
      (triHexTorusDualConfig L omega)


noncomputable def triHexTorusDefectWeightedDualPartitionSum
    (L : ℕ) [Fact (2 < L)] (pDual q : ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 (TorusSite L)),
    FK.fkWeight (hexagonalTorusGraph L) pDual q
        (triHexTorusDualConfig L omega) *
      q ^ triHexTorusDefect L
        (FK.openSub (triangularTorusGraph L) omega)


noncomputable def triHexTorusPrimalNumerator
    (L : ℕ) [Fact (2 < L)] (p q : ℝ)
    (F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 (TorusSite L)),
    F (triHexTorusDualConfig L omega) *
      FK.fkWeight (triangularTorusGraph L) p q omega


noncomputable def triHexTorusDualNumerator
    (L : ℕ) [Fact (2 < L)] (pDual q : ℝ)
    (F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 (TorusSite L)),
    F (triHexTorusDualConfig L omega) *
      FK.fkWeight (hexagonalTorusGraph L) pDual q
        (triHexTorusDualConfig L omega)


noncomputable def triHexTorusDefectWeightedDualNumerator
    (L : ℕ) [Fact (2 < L)] (pDual q : ℝ)
    (F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 (TorusSite L)),
    F (triHexTorusDualConfig L omega) *
      FK.fkWeight (hexagonalTorusGraph L) pDual q
        (triHexTorusDualConfig L omega) *
      q ^ triHexTorusDefect L
        (FK.openSub (triangularTorusGraph L) omega)


end PeriodicPlanar
end FK
end StatMech
