/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariantTwist.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Twists
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Twists

noncomputable section

open WeierstrassCurve Polynomial

universe u

variable {k : Type u} [Field k]
