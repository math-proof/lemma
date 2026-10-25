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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section24.Part3
open CategoryTheory MonoidalCategory Limits


noncomputable section

namespace UniversalCoefficientTheorem

/-- The short complex of chain complexes obtained by tensoring $C_*$ degreewise with the
short exact sequence $0 \to P_1 \to P_0 \to M \to 0$ extracted from a projective resolution
$P_\bullet$ of $M$. -/
def resSES (R : Type*) [CommRing R]
    (C : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R)
    (P : ProjectiveResolution M) :
    CategoryTheory.ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  CategoryTheory.ShortComplex.mk
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map (P.complex.d 1 0))
      (ComplexShape.down ℕ)).app C)
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map (P.π.f 0))
      (ComplexShape.down ℕ)).app C)
    (by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
        ← (tensoringRight (ModuleCat R)).map_comp, res_d_comp_pi_zero R M P, Functor.map_zero]
      ext i : 1
      simp only [NatTrans.mapHomologicalComplex, HomologicalComplex.zero_f_apply]
      rfl)

end UniversalCoefficientTheorem
end
