/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/InversionSet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation

open Finset BigOperators

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The bilinear inversion set of a word $w$: the set of $s \in S$ for which the
$s$-component of $\sigma_w(\alpha_s)$ is strictly negative. -/
noncomputable def bilinInversions (M : CoxeterMatrix B) (word : List B) : Finset B :=
  Finset.univ.filter (fun s => wordSigma M word (e s) s < 0)
