/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
open Finset BigOperators


namespace BooleanFourier

noncomputable def boolToReal (b : Bool) : ℝ :=
  if b then 1 else -1

noncomputable def chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  ∏ i ∈ S, boolToReal (x i)

noncomputable def fourierCoeff {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n)) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x * chi S x

def flipAt {n : ℕ} (j : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  Function.update x j (!x j)

noncomputable def levelComponent {n : ℕ} (k : ℕ) (f : (Fin n → Bool) → ℝ)
    (x : Fin n → Bool) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = k),
    fourierCoeff f S * chi S x

noncomputable def degree {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℕ :=
  Finset.sup (Finset.univ.filter (fun S : Finset (Fin n) => fourierCoeff f S ≠ 0))
    Finset.card

end BooleanFourier
