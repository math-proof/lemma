/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section24.Part3

@[expose] public section

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
