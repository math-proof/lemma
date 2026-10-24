/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.IwahoriGLnExistence
import Lemma.Matrix.Any_And_In_LowerUnipAndIn_DiagAndIn_UpperUnip.of.In_IwahoriGLn
import Lemma.Fin.ExtMulVal.eq.MulVal.of.In_DiagGLn
import sympy.atlas.v1.Atlas.Buildings.code.Building.IwahoriGLnUniqueness

open Matrix

namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

variable [DVRClosureGL2 C]

section GLn

variable (n : ℕ)
