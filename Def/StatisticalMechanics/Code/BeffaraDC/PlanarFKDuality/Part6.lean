/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part5
open Finset SimpleGraph Set


namespace StatMech

namespace BeffaraDC

open Lattice Ising Walls


noncomputable def pfdDualZ (P : PlanarZ2Subgraph) (p q : ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 P.V),
    pfdDualWeight P p q (FK.openSub P.G omega)


noncomputable def pfdDualProb (P : PlanarZ2Subgraph) (p q : ℝ)
    (omega : ConfigSpace (Sym2 P.V)) : ℝ :=
  pfdDualWeight P p q (FK.openSub P.G omega) / pfdDualZ P p q

end BeffaraDC
end StatMech
