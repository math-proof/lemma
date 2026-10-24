/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/UnramBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.NumberTheoryI.code.LocalExtensions
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.LocalExtensions
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.ResidueFieldFunctor
import sympy.atlas.v1.Atlas.NumberTheoryI.code.ResidueFieldFunctor
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Finite

noncomputable section

open Ideal Polynomial IsLocalRing

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 80000 in
