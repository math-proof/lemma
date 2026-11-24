module
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Module.Projective
public import Def.v1.Atlas.AlgebraicTopologyI.code.FundamentalThm.Part5
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.FundamentalThm
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section22


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section22.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace FundamentalHomologicalAlgebra

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The chain map `lift f P Q` covers `f`: composing it with the
augmentation of `Q` agrees with composing the augmentation of `P` with the
chain map associated to `f`.  This is the commutativity clause in the
Fundamental Theorem (Theorem 22.1). -/
theorem lift_commutes {Y Z : C}
    (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : FundamentalThm.Resolution Z) :
    lift f P Q ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f :=
  FundamentalThm.lift_commutes f P Q

end FundamentalHomologicalAlgebra
