/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section7.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.CrossProductExistence
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section8
import Def.v1.Atlas.AlgebraicTopologyI.code.CrossProductExistence.Part3
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section8.Part3
open ExactSequence


namespace HomologyCrossProduct

/-- A graded bilinear pairing of integer-indexed chain complexes
`A_* × B_* → C_*`: in every bidegree `(p, q)` a bilinear map
`A_p × B_q → C_{p+q}` satisfying the Leibniz rule
`d(a × b) = (da) × b + (-1)^p a × db` together with the boundary conditions
that cross-multiplying a boundary with a cycle (in either argument) lands in
the boundaries. These are exactly the data needed by Lemma 7.1 to induce a
bilinear pairing on homology. -/
structure GradedBilinearMap (A B C : IntChainComplex) where
  cross : ∀ (p q : ℤ), A.X p →+ (B.X q →+ C.X (p + q))
  leibniz_d : ∀ (p q : ℤ) (a : A.X p) (b : B.X q),
    C.d (p + q) ((cross p q) a b) =
      C.castHom (show (p - 1) + q = p + q - 1 by omega)
        ((cross (p - 1) q) (A.d p a) b) +
      (-1 : ℤ) ^ p.toNat •
        C.castHom (show p + (q - 1) = p + q - 1 by omega)
          ((cross p (q - 1)) a (B.d q b))
  cross_boundary_left : ∀ (p q : ℤ) (a_bar : A.X (p + 1)) (b : B.X q),
    b ∈ B.cycles q →
    (cross p q) (A.d' p a_bar) b ∈ C.boundaries (p + q)
  cross_boundary_right : ∀ (p q : ℤ) (a : A.X p) (b_bar : B.X (q + 1)),
    a ∈ A.cycles p →
    (cross p q) a (B.d' q b_bar) ∈ C.boundaries (p + q)

end HomologyCrossProduct
