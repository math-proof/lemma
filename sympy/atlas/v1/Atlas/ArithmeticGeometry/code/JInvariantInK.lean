/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariantInK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.JInvariant
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.JInvariant

noncomputable section

universe u

open WeierstrassCurve

variable {k : Type u} [Field k]
