/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/Certifiable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.WeightedCertificates
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter9.WeightedCertificates
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Certifiable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option maxHeartbeats 800000

open MeasureTheory Real Finset Set


noncomputable section

namespace TalagrandCertifiable

variable {n : ℕ} {Ω : Fin n → Type*}

/-- A function $f$ is Hamming-Lipschitz if $|f(x) - f(y)|$ is at most the Hamming distance
between $x$ and $y$ (the number of coordinates where they differ). -/
def IsHammingLipschitz [∀ i, DecidableEq (Ω i)]
    (f : ((i : Fin n) → Ω i) → ℝ) : Prop :=
  ∀ x y : (i : Fin n) → Ω i,
    |f x - f y| ≤ (Finset.univ.filter fun i => x i ≠ y i).card

/-- The upper level set $\{x : f(x) \geq r\}$ is $s$-certifiable (Definition 9.5.20). -/
def UpperLevelCertifiable [∀ i, DecidableEq (Ω i)]
    (f : ((i : Fin n) → Ω i) → ℝ) (r : ℝ) (s : ℕ) : Prop :=
  Certifiable.IsCertifiable (Ω := Ω) s {x | f x ≥ r}

/-- Key lemma for Talagrand's certifiable functions inequality: if $\{f \geq r\}$ is
$s$-certifiable, $f$ is Hamming-Lipschitz, and $f(y) \geq r$, then the convex distance from
$y$ to $\{f \leq r - t\}$ is at least $t / \sqrt{s}$. -/
def IsMedianPi
    {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : Fin n) → Measure (Ω i))
    (f : ((i : Fin n) → Ω i) → ℝ)
    (m : ℝ) : Prop :=
  (1 : ℝ) / 2 ≤ (Measure.pi μ {x | f x ≤ m}).toReal ∧
  (1 : ℝ) / 2 ≤ (Measure.pi μ {x | f x ≥ m}).toReal

end TalagrandCertifiable
end
