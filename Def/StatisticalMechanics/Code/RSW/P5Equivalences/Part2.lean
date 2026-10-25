/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/P5Equivalences.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.P5Equivalences
open Set


namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice

open StatMech.TwoDim


def rp5_P5a (μ : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c ≤ μ n (annulusEvent n)


def rp5_P5b (ν : ℕ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ) : Prop :=
  ∀ R : ℕ, 2 ≤ R → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c ≤ ν R n (annulusEvent n)


end Box
end RSW
end StatMech
