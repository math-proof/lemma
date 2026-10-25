/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section10.Part6
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace Excision

open AlgebraicTopology Set

noncomputable section

attribute [instance] subspaceChainInclusion_mono

/-- **Abstract second isomorphism theorem.** *For morphisms `φ : 𝒜 → 𝒳` and `ψ : ℬ → 𝒳` in
an abelian category, there is a canonical isomorphism*
$$(\mathcal{A} + \mathcal{B}) / \mathcal{A} \;\cong\; \mathcal{B} / (\mathcal{A} \cap \mathcal{B}),$$
*where `𝒜 + ℬ` is the image of `[φ, ψ] : 𝒜 ⊕ ℬ → 𝒳` and `𝒜 ∩ ℬ` is the pullback of `φ`
along `ψ`.* -/
def secondIsoOfMorphisms :
    cokernel (biprod.inl (X := 𝒜) (Y := ℬ) ≫ factorThruImage (biprod.desc φ ψ)) ≅
    cokernel (pullback.snd (f := φ) (g := ψ)) where
  hom := secondIso_inv φ ψ
  inv := secondIso_fwd φ ψ
  hom_inv_id := secondIso_inv_fwd_id φ ψ
  inv_hom_id := secondIso_fwd_inv_id φ ψ

end SecondIsoAbstract


/-- The concrete forward map for the second isomorphism applied to chain complexes:
`C^{\{A, B\}}_*(X) → C_*(B, A ∩ B)`. -/

end

/-- **Theorem 10.2 (Excision).** *Let `(X, A, U)` be an excisive triple, meaning
`closure U ⊆ interior A`. Then for every `n`, the pair inclusion*
$$(X \setminus U,\; A \setminus U) \hookrightarrow (X, A)$$
*induces an isomorphism on relative singular homology*
$$H_n(X \setminus U,\; A \setminus U;\, \mathbb{Z}) \;\xrightarrow{\sim}\; H_n(X, A;\, \mathbb{Z}).$$

Proved by passing to small chains via the locality principle and the second isomorphism. -/

namespace SphereHomology

/-- The `n`-sphere `S^n = \{x \in \mathbb{R}^{n+1} : \|x\| = 1\}`. -/
def Sphere (n : ℕ) : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

end SphereHomology
