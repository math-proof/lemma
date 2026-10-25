/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ClassInstances.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.GeometryOfManifolds.code.PolynomialDFS.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.PolynomialDFS
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.TwoDimDFS
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AlmostComplexManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.MoserDarboux
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.FourManifoldsSW
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ArnoldConjecture
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.PontrjaginObstructions
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HodgeTheory
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ChernClassProperties
import Instance.v1.Atlas.GeometryOfManifolds.code.TrivialDFS
import Def.v1.Atlas.GeometryOfManifolds.code.TwoDimDFS.Part3
import Structure.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part4
import Structure.v1.Atlas.GeometryOfManifolds.code.MoserDarboux.Part2
import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part8
import Class.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture.Part4
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
import Class.v1.Atlas.GeometryOfManifolds.code.HardLefschetz
import Structure.v1.Atlas.GeometryOfManifolds.code.PontrjaginObstructions.Part7
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part12
import Def.v1.Atlas.GeometryOfManifolds.code.ChernClassProperties.Part2
import Instance.v1.Atlas.GeometryOfManifolds.code.ClassInstances
set_option autoImplicit false
set_option maxHeartbeats 800000


/-- Model 4-dimensional Euclidean space $\mathbb{R}^4$, used as a charted space target for
4-manifolds. -/
abbrev E4Model := EuclideanSpace ℝ (Fin 4)

