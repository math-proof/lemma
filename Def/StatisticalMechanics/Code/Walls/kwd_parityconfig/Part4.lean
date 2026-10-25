/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.kwd_parityconfig.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Walls

section ParityProp

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (δ : Finset (Sym2 V))


noncomputable def parityProp (hG : G.Preconnected) (v₀ : V) : V → Bool :=
  fun v => walkPar G δ (hG v₀ v).some

end ParityProp
end StatMech.Walls
