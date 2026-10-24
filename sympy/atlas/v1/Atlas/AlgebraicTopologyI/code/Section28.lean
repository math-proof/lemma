/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section28.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Constructions.SumProd

open SimplexCategory CategoryTheory

noncomputable section

namespace ProductsInCohomology

/-- The simplex-category morphism $[p] \hookrightarrow [p+q]$ that picks out the front
$p$-face $\langle v_0, \ldots, v_p\rangle$ of the $(p+q)$-simplex. -/
def frontFace (p q : ℕ) : SimplexCategory.mk p ⟶ SimplexCategory.mk (p + q) :=
  SimplexCategory.Hom.mk ⟨fun i => ⟨i.val, by
    have := i.isLt; simp only [SimplexCategory.len_mk] at *; omega⟩,
  fun _ _ h => by simp only [Fin.mk_le_mk]; exact h⟩

/-- The simplex-category morphism $[q] \hookrightarrow [p+q]$ that picks out the back
$q$-face $\langle v_p, \ldots, v_{p+q}\rangle$ of the $(p+q)$-simplex. -/
def backFace (p q : ℕ) : SimplexCategory.mk q ⟶ SimplexCategory.mk (p + q) :=
  SimplexCategory.Hom.mk ⟨fun j => ⟨j.val + p, by
    have := j.isLt; simp only [SimplexCategory.len_mk] at *; omega⟩,
  fun _ _ h => by simp only [Fin.mk_le_mk]; omega⟩

/-- Continuous-map realisation of `frontFace`: the inclusion
$\Delta^p \hookrightarrow \Delta^{p+q}$ of the front face on topological standard simplices. -/
def frontFaceMap (p q : ℕ) :
    C(↥(stdSimplex ℝ (Fin (p + 1))), ↥(stdSimplex ℝ (Fin (p + q + 1)))) :=
  ⟨stdSimplex.map (frontFace p q).toOrderHom,
   stdSimplex.continuous_map (frontFace p q).toOrderHom⟩

/-- Continuous-map realisation of `backFace`: the inclusion
$\Delta^q \hookrightarrow \Delta^{p+q}$ of the back face on topological standard simplices. -/
def backFaceMap (p q : ℕ) :
    C(↥(stdSimplex ℝ (Fin (q + 1))), ↥(stdSimplex ℝ (Fin (p + q + 1)))) :=
  ⟨stdSimplex.map (backFace p q).toOrderHom,
   stdSimplex.continuous_map (backFace p q).toOrderHom⟩

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Front projection of a $(p+q)$-simplex $\sigma$ of $X \times Y$: the $p$-simplex of $X$
obtained by restricting to the front face and projecting on the first factor. The "front"
half of the Alexander-Whitney decomposition. -/
def frontProjection (p q : ℕ)
    (σ : C(↥(stdSimplex ℝ (Fin (p + q + 1))), X × Y)) :
    C(↥(stdSimplex ℝ (Fin (p + 1))), X) :=
  ⟨fun t => (σ (frontFaceMap p q t)).1,
   (continuous_fst.comp σ.continuous).comp (frontFaceMap p q).continuous⟩

/-- Back projection of a $(p+q)$-simplex $\sigma$ of $X \times Y$: the $q$-simplex of $Y$
obtained by restricting to the back face and projecting on the second factor. The "back"
half of the Alexander-Whitney decomposition. -/
def backProjection (p q : ℕ)
    (σ : C(↥(stdSimplex ℝ (Fin (p + q + 1))), X × Y)) :
    C(↥(stdSimplex ℝ (Fin (q + 1))), Y) :=
  ⟨fun t => (σ (backFaceMap p q t)).2,
   (continuous_snd.comp σ.continuous).comp (backFaceMap p q).continuous⟩

/-- **Construction 28.1 (Alexander-Whitney map).** The natural chain map
$\alpha : S_{p+q}(X \times Y) \to S_p(X) \otimes S_q(Y)$ sending a $(p+q)$-simplex $\sigma$
of $X \times Y$ to the tensor of its front $p$-projection and back $q$-projection. -/
def alexanderWhitneyMap (p q : ℕ) :
    FreeAbelianGroup (C(↥(stdSimplex ℝ (Fin (p + q + 1))), X × Y)) →+
    TensorProduct ℤ
      (FreeAbelianGroup (C(↥(stdSimplex ℝ (Fin (p + 1))), X)))
      (FreeAbelianGroup (C(↥(stdSimplex ℝ (Fin (q + 1))), Y))) :=
  FreeAbelianGroup.lift (fun σ =>
    FreeAbelianGroup.of (frontProjection p q σ) ⊗ₜ[ℤ]
    FreeAbelianGroup.of (backProjection p q σ))

/-- **Definition 28.2 (cup product).** Alias for the `SingularCohomology.cupProduct`, the
multiplicative structure $\smile : H^p(X; R) \otimes H^q(X; R) \to H^{p+q}(X; R)$ defined via
pulling back the cohomology cross product along the diagonal. -/
def cupProduct := @SingularCohomology.cupProduct

/-- The cochain-level cross product: given cochains $f$ on $X$ (degree $p$) and $g$ on $Y$
(degree $q$), produces the cochain on $X \times Y$ (degree $p+q$) sending a simplex
$\sigma$ to $(-1)^{pq} f(\text{front}(\sigma)) \cdot g(\text{back}(\sigma))$. -/
def cochainCrossProduct {R : Type*} [CommRing R] (p q : ℕ)
    (f : C(↥(stdSimplex ℝ (Fin (p + 1))), X) → R)
    (g : C(↥(stdSimplex ℝ (Fin (q + 1))), Y) → R)
    (σ : C(↥(stdSimplex ℝ (Fin (p + q + 1))), X × Y)) : R :=
  (-1 : R) ^ (p * q) * f (frontProjection p q σ) * g (backProjection p q σ)

variable {Z : Type*} [TopologicalSpace Z]

/-- Re-associate a simplex of $X \times Y \times Z$ to a simplex of $(X \times Y) \times Z$,
by composing with the homeomorphism `Homeomorph.prodAssoc`. Used for comparing the two
ways of bracketing a triple cup product. -/
def reassocSimplex (n : ℕ)
    (σ : C(↥(stdSimplex ℝ (Fin (n + 1))), X × Y × Z)) :
    C(↥(stdSimplex ℝ (Fin (n + 1))), (X × Y) × Z) :=
  ((Homeomorph.prodAssoc X Y Z).symm : C(X × Y × Z, (X × Y) × Z)).comp σ

/-- Cast a simplex of dimension $n$ to dimension $m$ when $n = m$, by composing with the
canonical simplex isomorphism induced by `Fin.cast`. -/
def castSimplex {W : Type*} [TopologicalSpace W] (n m : ℕ) (h : n = m)
    (σ : C(↥(stdSimplex ℝ (Fin (n + 1))), W)) :
    C(↥(stdSimplex ℝ (Fin (m + 1))), W) :=
  σ.comp ⟨stdSimplex.map (Fin.cast (by omega : m + 1 = n + 1)),
          stdSimplex.continuous_map _⟩
