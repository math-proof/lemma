/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.HarperIsoperimetric
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Floor.Semiring
set_option maxHeartbeats 800000

open Finset Real HarperIsoperimetric

namespace RapidExpansion

/-- The **Hamming weight** of $x \in \{0, 1\}^n$, i.e. the number of coordinates equal to
`true`; defined as the Hamming distance from the all-`false` vector. -/
def hammingWt {n : ℕ} (x : HammingCube n) : ℕ :=
  hammingDist x (fun _ => false)

/-- The **open Hamming ball** of radius $r$ centred at the origin in $\{0, 1\}^n$:
$\{x : \operatorname{wt}(x) < r\}$. -/
def openHammingBall (n : ℕ) (r : ℕ) : Finset (HammingCube n) :=
  Finset.univ.filter (fun x => hammingWt x < r)

/-- The **bit-flip involution** on the Hamming cube: $(\operatorname{flip}(x))_i = \neg x_i$
for every coordinate $i$. -/
def bitFlip (n : ℕ) (x : HammingCube n) : HammingCube n :=
  fun i => !(x i)
