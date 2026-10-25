/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.FreeMultipointEdwardsSokal.Part2
import Mathlib.Algebra.BigOperators.Ring.Nat
open Set
open scoped BigOperators


namespace StatMech.FK

open StatMech.ConfigSpace

variable {V : Type*} (G : SimpleGraph V)

noncomputable def markedComponents (omega : ConfigSpace (Sym2 V))
    (A : Finset V) : Finset (openSub G omega).ConnectedComponent := by
  classical
  exact A.image fun x => (openSub G omega).connectedComponentMk x

end StatMech.FK
