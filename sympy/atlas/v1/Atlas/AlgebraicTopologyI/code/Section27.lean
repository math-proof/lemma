/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section27.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Projective

open CategoryTheory AlgebraicTopology Limits

noncomputable section

/-- **Definition 27.2.** The Ext-functor $\mathrm{Ext}^n_R(M, N)$ at level $n$, packaged
as a `ModuleCat R`. Concretely, this is the $n$-th cohomology of $\mathrm{Hom}_R(F_*, N)$
for any free resolution $0 \leftarrow M \leftarrow F_0 \leftarrow F_1 \leftarrow \cdots$,
realised here via the derived functor `Ext` on the abelian category of `R`-modules. -/
def ExtR (R : Type*) [CommRing R] (n : ℕ) (M N : ModuleCat R) : ModuleCat R :=
  ((Ext R (ModuleCat R) n).obj (Opposite.op M)).obj N

namespace UniversalCoefficientTheorem

/-- The underlying biproduct isomorphism behind the UCT: for a free chain complex $C_*$
over a PID $R$ and a coefficient module $N$, there is an iso
$\mathrm{Ext}^1(H_{n-1}, N) \oplus \mathrm{Hom}(H_n, N) \cong H^n(\mathrm{Hom}(C_*, N))$.
This is the unsplit form of Theorem 27.1, from which the split short exact sequence is
extracted by `splitting_from_biprod_iso`. -/
def uctInducedChainMap
    (R : Type) [CommRing R]
    {C D : ChainComplex (ModuleCat.{0} R) ℕ} (N : ModuleCat.{0} R) (φ : C ⟶ D) :
    D.linearYonedaObj R N ⟶ C.linearYonedaObj R N :=
  (HomologicalComplex.unopFunctor _ _).map
    ((((linearYoneda R (ModuleCat.{0} R)).obj N).rightOp.mapHomologicalComplex _).map φ).op

/-- The cochain map $\mathrm{Hom}(C_*, N) \to \mathrm{Hom}(C_*, N')$ induced by a coefficient
map $f : N \to N'$, used to phrase naturality of the UCT in the coefficient variable. -/
def uctInducedCoefficientMap
    (R : Type) [CommRing R]
    (C : ChainComplex (ModuleCat.{0} R) ℕ) {N N' : ModuleCat.{0} R} (f : N ⟶ N') :
    C.linearYonedaObj R N ⟶ C.linearYonedaObj R N' :=
  (HomologicalComplex.unopFunctor _ _).map
    (((((linearYoneda R (ModuleCat.{0} R)).map f).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).app C).op)

/-- Naturality of the UCT biproduct isomorphism in the chain-complex variable: a chain map
$\varphi : C_* \to D_*$ induces compatible maps on $\mathrm{Ext}^1(H_{n-1}(-), N)$,
$\mathrm{Hom}(H_n(-), N)$, and $H^n(\mathrm{Hom}(-, N))$, making the obvious square commute. -/
end UniversalCoefficientTheorem

namespace SingularCohomology

/-- The cap product $\cap : H^p(X; R) \otimes H_n(X; R) \to H_{n-p}(X; R)$ expressed as
the curried $R$-bilinear map $H^p(X; R) \to (H_n(X; R) \to H_{n-p}(X; R))$. Used downstream
for capping with the fundamental class in Poincaré duality. -/
abbrev singularChains (R : Type) [CommRing R] (X : TopCat.{0}) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  ((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X

/-- Each module of singular chains $S_i(X; R)$ is free over $R$ (with basis the singular
$i$-simplices). This is the hypothesis needed to apply the UCT (`cohomologyUCT`) to the
singular chain complex. -/
end SingularCohomology
