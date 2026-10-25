/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BourgainLemma2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace BourgainMultiscale

open Set MeasureTheory

/-- `IsAlmostLinear f a b t_I ε` says that on the interval $[a,b]$, $f$ is within $\varepsilon$
of the linear function $x \mapsto f(a) + t_I (x - a)$ of slope $t_I$. -/
def IsAlmostLinear (f : ℝ → ℝ) (a b : ℝ) (t_I : ℝ) (ε : ℝ) : Prop :=
  ∀ x ∈ Icc a b, |f x - (f a + t_I * (x - a))| ≤ ε

/-- `IsSemiWellSpaced f a b s` says that on the left half of $[a,b]$, $f$ grows at slope at
least $2-s$, and on the right half, $f$ grows at slope at least $s$ — encoding the
"semi-well-spaced" alternative of the multiscale decomposition. -/
def IsSemiWellSpaced (f : ℝ → ℝ) (a b : ℝ) (s : ℝ) : Prop :=
  let mid := (a + b) / 2
  (∀ x ∈ Icc a mid, f x ≥ f a + (2 - s) * (x - a)) ∧
  (∀ x ∈ Icc mid b, f x ≥ f mid + s * (x - mid))

end BourgainMultiscale
