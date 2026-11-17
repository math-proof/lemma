/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSimon
public section

open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


structure HighTempSwitchInput where
  F : Finset (Sym2 V)
  H : Finset (Sym2 V)
deriving DecidableEq, Fintype


structure HighTempSwitchOutput where
  x : V
  y : V
  A : Finset (Sym2 V)
  B : Finset (Sym2 V)
deriving DecidableEq, Fintype


end Sharpness
end StatMech
