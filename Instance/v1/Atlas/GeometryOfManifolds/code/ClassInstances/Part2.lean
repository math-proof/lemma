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
import Abbrev.v1.Atlas.GeometryOfManifolds.code.ClassInstances
set_option autoImplicit false
set_option maxHeartbeats 800000


/-- Trivial `Has4ManifoldTopology` instance on $\mathbb{R}^4$ with all intersection-form invariants
($b_2$, signature) set to zero and Euler characteristic $2$. -/
noncomputable instance trivialHas4ManifoldTopology : Has4ManifoldTopology E4Model where
  Q := {
    b₂ := 0
    b₂_plus := 0
    b₂_minus := 0
    rank_decomp := rfl
    signature := 0
    signature_eq := by norm_num
    isEven := false
    bilinForm := fun _ _ => 0
  }
  euler := 2
  euler_eq := by norm_num


