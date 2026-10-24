/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Retraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.ChamberComplex.Uniqueness
import Lemma.Finset.AgreeOnImage.of.AgreeOn
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import sympy.atlas.v1.Atlas.Buildings.code.Building.Basic

open scoped Classical

variable {V : Type*} [DecidableEq V]
