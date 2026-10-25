/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SharpSATInIP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.InteractiveProofs.Part2
import Def.v1.Atlas.TheoryOfComputation.code.SharpSAT
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring


namespace NPCompleteness

/--
Arithmetization of a Boolean formula: lifts a Boolean formula `φ` to a polynomial
expression over a commutative ring `R` using the standard encoding
`true ↦ 1`, `false ↦ 0`, `¬x ↦ 1 - x`, `x ∧ y ↦ x * y`, `x ∨ y ↦ x + y - x*y`.
This is the foundation of the sum-check protocol used to show `#SAT ∈ IP`.
-/
noncomputable def BoolFormula.arithEval {R : Type*} [CommRing R]
    (σ : ℕ → R) : BoolFormula → R
  | .var n => σ n
  | .trueConst => 1
  | .falseConst => 0
  | .not φ => 1 - φ.arithEval σ
  | .and φ ψ => φ.arithEval σ * ψ.arithEval σ
  | .or φ ψ => φ.arithEval σ + ψ.arithEval σ - φ.arithEval σ * ψ.arithEval σ

/--
Partial count: number of satisfying assignments of `φ` over `m` variables, where
the first `i` variables are fixed by `presets` and the remaining `m - i` are
quantified. Used to express intermediate sums in the sum-check protocol.
-/
noncomputable def BoolFormula.partialCount
    (φ : BoolFormula) (m i : ℕ) (presets : Fin i → Bool) : ℕ :=
  Finset.card (Finset.univ.filter (fun (σ : Fin (m - i) → Bool) =>
    φ.eval (fun k =>
      if h : k < i then presets ⟨k, h⟩
      else if h2 : k < m then σ ⟨k - i, by omega⟩
      else false) = true))

/--
Count of satisfying assignments of `φ` indexed by the first `m` Boolean
variables. Equivalent to `#SAT` for the formula `φ` when `m` bounds its
variable indices.
-/
noncomputable def BoolFormula.countSatFin (φ : BoolFormula) (m : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun (σ : Fin m → Bool) =>
    φ.eval (fun i => if h : i < m then σ ⟨i, h⟩ else false) = true))

end NPCompleteness
