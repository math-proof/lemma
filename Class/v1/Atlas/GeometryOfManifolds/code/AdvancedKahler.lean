/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ConnectionsCurvature
import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
set_option autoImplicit false

open DifferentialFormSpace


/-- A typeclass packaging the Hodge numbers $h^{p,q}(M)$ and Betti numbers $b_k(M)$
of a compact Kähler manifold, together with the basic symmetries they satisfy:
conjugation symmetry $h^{p,q} = h^{q,p}$, Hodge-star symmetry
$h^{p,q} = h^{n-q,\,n-p}$, and the link $b_k = \sum_{p+q=k} h^{p,q}$ from the
Hodge decomposition $H^k_{dR}(M,\mathbb{C}) = \bigoplus_{p+q=k} H^{p,q}_{\bar\partial}(M)$. -/
class HasHodgeNumbers
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF] where
  complexDim : ℕ
  hodge : ℕ → ℕ → ℕ
  conjugation_symmetry : ∀ p q, hodge p q = hodge q p
  star_symmetry : ∀ p q, hodge p q = hodge (complexDim - q) (complexDim - p)
  betti : ℕ → ℕ
  betti_hodge_link : ∀ (k : ℕ),
    betti k = (Finset.range (k + 1)).sum (fun p => hodge p (k - p))


/-- A cohomology structure equipped with iterated Lefschetz operators
$L^m : H^k(M) \to H^{k+2m}(M)$. On a compact Kähler manifold these
are the linear maps appearing in the Hard Lefschetz theorem. -/
class HasCohomologyWithLefschetz
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    extends @HasCohomology Ω VF inst where
  L_map : ∀ (k m : ℕ),
    @LinearMap ℝ ℝ _ _ (RingHom.id ℝ) (H k) (H (k + 2 * m))
      (H_addCommGroup k).toAddCommMonoid (H_addCommGroup (k + 2 * m)).toAddCommMonoid
      (H_module k) (H_module (k + 2 * m))


/-- A projective embedding datum for a symplectic manifold $(M, \omega)$:
an embedding $\iota : M \hookrightarrow N$ into a target carrying a closed
form $\omega_N$ such that $\iota^* \omega_N = \omega + d\alpha$ for some $\alpha \in \Omega^1(M)$.
This is the existence half of the Kodaira embedding theorem. -/
class HasProjectiveEmbedding
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) where
  embeddingDim : ℕ
  Ω_target : ℕ → Type*
  VF_target : Type*
  inst_target : DifferentialFormSpace Ω_target VF_target
  embedding : DFSMorphism Ω VF Ω_target VF_target
  targetForm : Ω_target 2
  targetForm_closed : inst_target.d targetForm = 0
  pullback_cohomologous : ∃ (α : Ω 1),
    @DFSMorphism.pullback _ _ _ _ inst inst_target embedding (p := 2) targetForm =
      S.ω + inst.d α

