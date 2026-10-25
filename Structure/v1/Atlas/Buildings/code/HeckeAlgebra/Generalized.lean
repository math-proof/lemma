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


namespace GeneralizedHecke

/-- Data of a generalized BN-pair on a group `G`: subgroups recording the label-preserving
subgroup, Borel, normalizer $N$, restricted normalizer $N ∩$ labelPreserving, the torus
$N ∩ B$, and the restricted torus, together with their intersection axioms. -/
structure GeneralizedBNPairData (G : Type*) [Group G] where
  labelPreserving : Subgroup G
  borel : Subgroup G
  normalizerN : Subgroup G
  normalizerRestricted : Subgroup G
  torus : Subgroup G
  torusRestricted : Subgroup G
  borel_in_labelPreserving : borel ≤ labelPreserving
  normalizerRestricted_eq : normalizerRestricted = normalizerN ⊓ labelPreserving
  torus_eq : torus = normalizerN ⊓ borel
  torusRestricted_eq : torusRestricted = normalizerRestricted ⊓ borel

end GeneralizedHecke
