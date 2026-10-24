/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/Generalized/Theorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.BNPair.Generalized.TypePreserving
import Lemma.Nat.Tt.le.Bt
import Lemma.Real.EqSigma.of.Ne

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {B_idx : Type*} [Fintype B_idx] [DecidableEq B_idx]

namespace GeneralizedBNPair

variable {Gt : Type*} [Group Gt] {M : CoxeterMatrix B_idx}
variable (gbp : GeneralizedBNPair Gt M)

/-- The Borel subgroup $B \leq G$ pushed forward to $\tilde G$ along the inclusion
$G \hookrightarrow \tilde G$. -/
def Blifted : Subgroup Gt :=
  gbp.strictBNPair.B.map gbp.G.subtype

/-- The subgroup $N \leq G$ pushed forward to $\tilde G$. -/
def Nlifted : Subgroup Gt :=
  gbp.strictBNPair.N.map gbp.G.subtype

/-- The torus $T = B \cap N \leq G$ pushed forward to $\tilde G$. -/
def Tlifted : Subgroup Gt :=
  gbp.strictBNPair.T.map gbp.G.subtype

/-- The intersection $\tilde T \cap G$ inside $\tilde G$; by the axioms this coincides
with the lifted $T$. -/
def TtInterG : Subgroup Gt :=
  gbp.Tt ⊓ gbp.G

/-- The subgroup $\tilde T \cap G$ pulled back into $\tilde T$, viewed as a subgroup
of $\tilde T$. Quotienting by this yields the twist group. -/
def twistSubgroup : Subgroup gbp.Tt :=
  (gbp.Tt ⊓ gbp.G).subgroupOf gbp.Tt

/-- The **twist group** $\tilde T / (\tilde T \cap G)$, finite by axiom, which measures
the non-type-preserving part of $\tilde G$. -/
def TwistGroup := gbp.Tt ⧸ gbp.twistSubgroup

/-- The "twisted" Bruhat cell $\sigma \cdot B \cdot w \cdot B \subseteq \tilde G$
for $\sigma \in \tilde T$ and $w \in W$: elements that can be written as
$\sigma \cdot b_1 \cdot n \cdot b_2$ with $b_i \in B$ (lifted) and $n$ an $N$-lift of $w$. -/
def bruhatCellGt (σ : Gt) (w : M.Group) : Set Gt :=
  { g : Gt | ∃ (b₁ : Gt) (_ : b₁ ∈ gbp.Blifted)
               (n : Gt) (_ : n ∈ gbp.Nlifted)
               (b₂ : Gt) (_ : b₂ ∈ gbp.Blifted),
    (∃ (n' : gbp.strictBNPair.N),
      gbp.strictBNPair.π n' = w ∧ (n' : Gt) = n) ∧
    g = σ * b₁ * n * b₂ }

/-- The left coset $\sigma B = \{\sigma b : b \in B\} \subseteq \tilde G$. -/
def sigmaB (σ : Gt) : Set Gt :=
  { g : Gt | ∃ (b : Gt) (_ : b ∈ gbp.Blifted), g = σ * b }

/-- The right coset $B\sigma = \{b\sigma : b \in B\} \subseteq \tilde G$. -/
def Bsigma (σ : Gt) : Set Gt :=
  { g : Gt | ∃ (b : Gt) (_ : b ∈ gbp.Blifted), g = b * σ }

end GeneralizedBNPair
