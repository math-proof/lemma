/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RingTheory.Flat.CategoryTheory
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section24
open CategoryTheory MonoidalCategory Limits


noncomputable section

namespace UniversalCoefficientTheorem

/-- Tor as the homology of a projective resolution: for any projective resolution $P_\bullet$
of $M$,
$$\operatorname{Tor}_1(X, M) \cong H_1(X \otimes P_\bullet).$$
Used to identify the connecting map of the UCT short exact sequence with the Tor term. -/
noncomputable def torIsoHomology (R : Type*) [CommRing R]
    [HasProjectiveResolutions (ModuleCat R)]
    (X M : ModuleCat R) (P : ProjectiveResolution M) :
    ((Tor (ModuleCat R) 1).obj X).obj M ≅
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).obj
        ((((tensoringLeft (ModuleCat R)).obj X).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex) :=
  P.isoLeftDerivedObj ((tensoringLeft (ModuleCat R)).obj X) 1

end UniversalCoefficientTheorem
end
