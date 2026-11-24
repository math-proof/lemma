module
public import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
public import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
open scoped BigOperators
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeSum.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]


def isingSumConfigEquiv : ConfigSpace (V ⊕ W) ≃ ConfigSpace V × ConfigSpace W :=
  Equiv.sumPiEquivProdPi (fun _ : V ⊕ W => Bool)

end Ising
end StatMech
