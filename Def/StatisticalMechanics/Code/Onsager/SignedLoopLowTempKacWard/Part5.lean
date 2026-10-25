/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempDual.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceClosure
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempKacWard.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

open StatMech.FrontierA

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

noncomputable def kwg_indexedEvenPolynomial (ends : E -> Sym2 V)
    (x : E -> ℂ) : ℂ :=
  ∑ F : Finset E,
    if kwg_IsEven ends F then ∏ e ∈ F, x e else 0

end
end StatMech.Onsager
