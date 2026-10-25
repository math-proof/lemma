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
import Abbrev.StatisticalMechanics.Code.Ising.KWGeometricDual.Part2
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


noncomputable def kwg_subdivGraph {V E : Type*} (ends : E → Sym2 V) :
    SimpleGraph (kwg_SubdivVertex V E) where
  Adj x y := match x, y with
    | Sum.inl v, Sum.inr (e, false) => v = (ends e).out.1
    | Sum.inl v, Sum.inr (e, true) => v = (ends e).out.2
    | Sum.inr (e, false), Sum.inl v => v = (ends e).out.1
    | Sum.inr (e, true), Sum.inl v => v = (ends e).out.2
    | Sum.inr (e, b), Sum.inr (e', b') => e = e' ∧ b ≠ b'
    | Sum.inl _, Sum.inl _ => False
  symm := by
    constructor
    intro x y
    rcases x with v | ⟨e, b⟩ <;> rcases y with w | ⟨e', b'⟩
    · simp
    · cases b' <;> simp [eq_comm]
    · cases b <;> simp [eq_comm]
    · cases b <;> cases b' <;> simp [eq_comm]
  loopless := ⟨by
    intro x
    rcases x with v | ⟨e, b⟩
    · simp
    · cases b <;> simp⟩

end Ising
end StatMech
