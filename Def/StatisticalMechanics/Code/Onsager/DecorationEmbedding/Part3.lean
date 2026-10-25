/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part2


namespace StatMech.Onsager

def ons_fourDirStepWalk (N : ℕ) [Fact (2 < N)]
    (r : Fin 4 → Fin 4) (p : ZMod N × ZMod N) :
    (onsTorusGraph N).Walk p (ons_fourDirSteps N r p) :=
  .cons (ons_torusAdj_dirStep N p (r 0))
    (.cons (ons_torusAdj_dirStep N (ons_dirStep N (r 0) p) (r 1))
      (.cons (ons_torusAdj_dirStep N
          (ons_dirStep N (r 1) (ons_dirStep N (r 0) p)) (r 2))
        (.cons (ons_torusAdj_dirStep N
            (ons_dirStep N (r 2)
              (ons_dirStep N (r 1) (ons_dirStep N (r 0) p))) (r 3))
          .nil)))


def ons_decEmbedGraph (L : ℕ) [Fact (2 < L)] :
    SimpleGraph (ZMod (8 * L) × ZMod (8 * L)) := by
  letI : Fact (2 < 8 * L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  exact onsTorusGraph (8 * L)

end StatMech.Onsager
