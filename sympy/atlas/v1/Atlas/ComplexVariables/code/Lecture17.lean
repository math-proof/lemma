/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture17.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option autoImplicit false

open Finset Filter Topology BigOperators Set Polynomial Complex

set_option maxHeartbeats 800000

noncomputable def singularPart (P : Polynomial ℂ) (b : ℂ) (z : ℂ) : ℂ :=
  Polynomial.eval (1 / (z - b)) P

def HasNoConstantTerm (P : Polynomial ℂ) : Prop :=
  Polynomial.eval (0 : ℂ) P = 0

def HasSingularPartAt (f : ℂ → ℂ) (P : Polynomial ℂ) (b : ℂ) : Prop :=
  AnalyticAt ℂ (fun z => f z - singularPart P b z) b

noncomputable def hFunc (b : ℕ → ℂ) (P : ℕ → Polynomial ℂ) (p : ℕ → Polynomial ℂ) (z : ℂ) : ℂ :=
  ∑' ν, (singularPart (P ν) (b ν) z - Polynomial.eval z (p ν))
