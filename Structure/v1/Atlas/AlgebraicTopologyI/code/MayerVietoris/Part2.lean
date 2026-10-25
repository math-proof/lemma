/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.MayerVietoris
open Set Topology EilenbergSteenrod Function

universe u


namespace MayerVietoris

attribute [instance] MayerVietorisCover.instTop

/-- The Mayer-Vietoris long exact sequence for a homology theory `h` and a cover `c`
(Theorem 11.5): connecting homomorphisms `∂ : H_{n+1}(X) →+ H_n(A ∩ B)` together with
exactness of the long sequence
`⋯ → H_n(A ∩ B) → H_n(A) ⊕ H_n(B) → H_n(X) → H_{n-1}(A ∩ B) → ⋯`,
where the first map is `[j_{1*}, -j_{2*}]` and the second is `i_{1*} + i_{2*}`. -/
structure MayerVietorisSequence (h : HomologyTheory) (c : MayerVietorisCover) where
  connecting : ∀ (n : ℤ), h.H (n + 1) c.pairX →+ h.H n c.pairAB
  exact_at_prod : ∀ (n : ℤ),
    Exact
      (fun x => (h.map n c.inclAB_A x, -(h.map n c.inclAB_B x)))
      (fun p : h.H n c.pairA × h.H n c.pairB =>
        h.map n c.inclA_X p.1 + h.map n c.inclB_X p.2)
  exact_at_X : ∀ (n : ℤ),
    Exact
      (fun p : h.H (n + 1) c.pairA × h.H (n + 1) c.pairB =>
        h.map (n + 1) c.inclA_X p.1 + h.map (n + 1) c.inclB_X p.2)
      (connecting n)
  exact_at_AB : ∀ (n : ℤ),
    Exact
      (connecting n)
      (fun x => (h.map n c.inclAB_A x, -(h.map n c.inclAB_B x)))

end MayerVietoris
