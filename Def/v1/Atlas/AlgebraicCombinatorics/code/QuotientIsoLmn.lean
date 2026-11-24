module
public import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WreathOrbits.Part5
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.WreathOrbits
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
public import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
set_option autoImplicit false
set_option maxHeartbeats 800000
open WreathOrbits YoungLattice YoungLattice.Lmn


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace QuotientIsoLmn

variable {m n : ℕ}

def GridYoungDiagram (m n : ℕ) : Type :=
  {S : Finset (Fin m × Fin n) // WreathOrbits.IsGridYoung S}

end QuotientIsoLmn
