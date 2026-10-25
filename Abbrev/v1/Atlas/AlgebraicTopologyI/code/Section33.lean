/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section33.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
open CategoryTheory AlgebraicTopology Limits


noncomputable section

namespace SingularCohomology

variable (R : Type) [CommRing R]

/-- The singular chain complex $S_\bullet(X; R)$ of a topological space `X` with
coefficients in the ring `R`, as a chain complex of `R`-modules. -/
abbrev singularChainCx (X : TopCat.{0}) :=
  (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X)

/-- The $p$-th singular cohomology module $H^p(X; R)$ of `X` with coefficients
in `R`, computed as the $p$-th cohomology of the dual cochain complex
$\mathrm{Hom}_R(S_\bullet(X; R), R)$. -/
abbrev singularCohomologyR (X : TopCat.{0}) (p : ℕ) : ModuleCat R :=
  ((singularChainCx R X).linearYonedaObj R (ModuleCat.of R R)).homology p

end SingularCohomology
end
