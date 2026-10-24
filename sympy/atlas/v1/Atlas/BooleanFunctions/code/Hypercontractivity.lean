/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Hypercontractivity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Parseval
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.TwoPointInequality
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Definitions
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Parseval
import sympy.atlas.v1.Atlas.BooleanFunctions.code.TwoPointInequality
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.MeanInequalitiesPow

open Finset BigOperators Real

namespace BooleanFourier

noncomputable def noiseOp {n : ℕ} (ρ : ℝ) (f : BoolFn n) : BoolFn n :=
  fun x => ∑ y : Fin n → Bool,
    (∏ i : Fin n, ((1 + ρ * boolToReal (x i) * boolToReal (y i)) / 2)) * f y

noncomputable def restrictLast {n : ℕ} (f : BoolFn (n + 1)) (b : Bool) : BoolFn n :=
  fun x => f (Fin.snoc x b)

noncomputable def combineAssignment {n : ℕ} (J : Finset (Fin n))
    (xJ : ↥J → Bool) (z : ↥(Jᶜ) → Bool) : Fin n → Bool :=
  fun i => if h : i ∈ J then xJ ⟨i, h⟩ else z ⟨i, Finset.mem_compl.mpr h⟩

noncomputable def restrictToSubset {n : ℕ} (J : Finset (Fin n))
    (f : BoolFn n) (z : ↥(Jᶜ) → Bool) : (↥J → Bool) → ℝ :=
  fun xJ => f (combineAssignment J xJ z)

noncomputable def chiOn {n : ℕ} (J : Finset (Fin n)) (S : Finset ↥J)
    (x : ↥J → Bool) : ℝ :=
  ∏ i ∈ S, boolToReal (x i)

noncomputable def fourierCoeffOn {n : ℕ} (J : Finset (Fin n))
    (g : (↥J → Bool) → ℝ) (S : Finset ↥J) : ℝ :=
  (1 / (2 : ℝ) ^ J.card) * ∑ x : ↥J → Bool, g x * chiOn J S x
