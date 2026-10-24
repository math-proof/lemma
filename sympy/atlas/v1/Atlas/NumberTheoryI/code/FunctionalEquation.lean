/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FunctionalEquation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

open Complex hiding exp continuous_exp
open Real Filter Topology Asymptotics

noncomputable section

namespace FunctionalEquation

abbrev completedZeta (s : ℂ) : ℂ := completedRiemannZeta s

abbrev completedZeta₀ (s : ℂ) : ℂ := completedRiemannZeta₀ s

def xi (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2
