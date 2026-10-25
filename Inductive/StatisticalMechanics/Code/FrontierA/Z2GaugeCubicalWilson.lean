/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalWilson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Structure.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalWilson
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

inductive CubicalEdge (a b c : Nat)
  | x : Fin a → Fin (b + 1) → Fin (c + 1) → CubicalEdge a b c
  | y : Fin (a + 1) → Fin b → Fin (c + 1) → CubicalEdge a b c
  | z : Fin (a + 1) → Fin (b + 1) → Fin c → CubicalEdge a b c
  deriving DecidableEq, Fintype


inductive CubicalPlaquette (a b c : Nat)
  | xy : Fin a → Fin b → Fin (c + 1) → CubicalPlaquette a b c
  | xz : Fin a → Fin (b + 1) → Fin c → CubicalPlaquette a b c
  | yz : Fin (a + 1) → Fin b → Fin c → CubicalPlaquette a b c
  deriving DecidableEq, Fintype


end
end StatMech.FrontierA
