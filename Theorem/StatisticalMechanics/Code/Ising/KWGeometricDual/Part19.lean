/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Graph.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Ising.KWGeometricDual.Part20
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


@[simp] theorem kwg_subdivGraph_face_port_false {V E : Type*} (ends : E → Sym2 V)
    (v : V) (e : E) :
    (kwg_subdivGraph ends).Adj (Sum.inl v) (Sum.inr (e, false)) ↔
      v = (ends e).out.1 := Iff.rfl

@[simp] theorem kwg_subdivGraph_face_port_true {V E : Type*} (ends : E → Sym2 V)
    (v : V) (e : E) :
    (kwg_subdivGraph ends).Adj (Sum.inl v) (Sum.inr (e, true)) ↔
      v = (ends e).out.2 := Iff.rfl

@[simp] theorem kwg_subdivGraph_ports {V E : Type*} (ends : E → Sym2 V)
    (e e' : E) (b b' : Bool) :
    (kwg_subdivGraph ends).Adj (Sum.inr (e, b)) (Sum.inr (e', b')) ↔
      e = e' ∧ b ≠ b' := by cases b <;> cases b' <;> rfl

end Ising
end StatMech
