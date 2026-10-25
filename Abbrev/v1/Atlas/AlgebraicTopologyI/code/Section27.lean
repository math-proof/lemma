/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section27.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Projective
import Def.v1.Atlas.AlgebraicTopologyI.code.Section27
open CategoryTheory AlgebraicTopology Limits


noncomputable section

namespace SingularCohomology

/-- The cap product $\cap : H^p(X; R) \otimes H_n(X; R) \to H_{n-p}(X; R)$ expressed as
the curried $R$-bilinear map $H^p(X; R) \to (H_n(X; R) \to H_{n-p}(X; R))$. Used downstream
for capping with the fundamental class in Poincaré duality. -/
abbrev singularChains (R : Type) [CommRing R] (X : TopCat.{0}) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  ((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X

end SingularCohomology
end
