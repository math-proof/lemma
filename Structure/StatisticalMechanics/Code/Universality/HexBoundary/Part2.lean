/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexBoundary.Part2


namespace StatMech.Universality

open Complex Filter Topology

open scoped Topology Real BigOperators


namespace HexDomain

variable {V : Type*} [DecidableEq V] (D : HexDomain V)


structure InteriorPairing where
  
  interior : Finset (HexIncidence V)
  
  pair : HexIncidence V → HexIncidence V
  
  pair_mem : ∀ e ∈ interior, pair e ∈ interior
  
  pair_invol : ∀ e ∈ interior, pair (pair e) = e
  
  pair_ne : ∀ e ∈ interior, pair e ≠ e
  
  cancel : ∀ e ∈ interior, D.incTerm e = - D.incTerm (pair e)

end HexDomain
end StatMech.Universality
