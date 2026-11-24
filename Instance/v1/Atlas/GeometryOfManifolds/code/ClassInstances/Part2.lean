module
public import Instance.v1.Atlas.GeometryOfManifolds.code.PolynomialDFS.Part3
public import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.PolynomialDFS
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.TwoDimDFS
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.AlmostComplexManifolds
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.MoserDarboux
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.FourManifoldsSW
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.ArnoldConjecture
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.PontrjaginObstructions
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.HodgeTheory
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.ChernClassProperties
public import Instance.v1.Atlas.GeometryOfManifolds.code.TrivialDFS
public import Def.v1.Atlas.GeometryOfManifolds.code.TwoDimDFS.Part3
public import Structure.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part4
public import Structure.v1.Atlas.GeometryOfManifolds.code.MoserDarboux.Part2
public import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part8
public import Class.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture.Part4
public import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
public import Class.v1.Atlas.GeometryOfManifolds.code.HardLefschetz
public import Structure.v1.Atlas.GeometryOfManifolds.code.PontrjaginObstructions.Part7
public import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part12
public import Def.v1.Atlas.GeometryOfManifolds.code.ChernClassProperties.Part2
public import Abbrev.v1.Atlas.GeometryOfManifolds.code.ClassInstances
set_option autoImplicit false
set_option maxHeartbeats 800000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ClassInstances.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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


