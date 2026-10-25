/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generalized.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Structure.v1.Atlas.Buildings.code.HeckeAlgebra.Generalized


namespace GeneralizedHecke

/-- Property: the Borel sits inside the label-preserving subgroup. -/
def GeneralizedBNPairData.BorelInLabelPreserving {G : Type*} [Group G]
    (d : GeneralizedBNPairData G) : Prop :=
  d.borel ≤ d.labelPreserving

/-- Property: the restricted normalizer is exactly the intersection of $N$ with the
label-preserving subgroup. -/
def GeneralizedBNPairData.NormalizerRestrictedIsIntersection {G : Type*} [Group G]
    (d : GeneralizedBNPairData G) : Prop :=
  ∀ g : G, g ∈ d.normalizerRestricted ↔ g ∈ d.normalizerN ∧ g ∈ d.labelPreserving

/-- Property: the torus $T = N ∩ B$. -/
def GeneralizedBNPairData.TorusIsIntersection {G : Type*} [Group G]
    (d : GeneralizedBNPairData G) : Prop :=
  ∀ g : G, g ∈ d.torus ↔ g ∈ d.normalizerN ∧ g ∈ d.borel

/-- Property: the restricted torus equals $N_{\text{res}} ∩ B$. -/
def GeneralizedBNPairData.TorusRestrictedIsIntersection {G : Type*} [Group G]
    (d : GeneralizedBNPairData G) : Prop :=
  ∀ g : G, g ∈ d.torusRestricted ↔ g ∈ d.normalizerRestricted ∧ g ∈ d.borel

/-- A function $f : G → R$ is $B$-bi-invariant if $f(b_1 g b_2) = f(g)$ for all
$b_1, b_2 ∈ B$ and all $g ∈ G$. -/
def BiInvariantFunction {G R : Type*} [Group G] (B : Subgroup G) (f : G → R) : Prop :=
  ∀ (b₁ b₂ : G), b₁ ∈ B → b₂ ∈ B → ∀ g, f (b₁ * g * b₂) = f g

end GeneralizedHecke
