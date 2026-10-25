/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryRusso.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.RussoDerivative.Part5
open scoped BigOperators
open Finset


namespace StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (C : SimpleGraph V) [DecidableRel C.Adj]


noncomputable def bcMean (p q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  ∑ ω, g ω * bcProb G C p q ω


noncomputable def bcCov (p q : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  bcMean G C p q (fun ω => f ω * g ω) - bcMean G C p q f * bcMean G C p q g


noncomputable def bcNumer (p q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  ∑ ω, g ω * bcWeight G C p q ω


noncomputable def bcProbOf (p q : ℝ) (A : Set (ConfigSpace (Sym2 V))) : ℝ :=
  bcMean G C p q (A.indicator fun _ => (1 : ℝ))

end StatMech.FK
