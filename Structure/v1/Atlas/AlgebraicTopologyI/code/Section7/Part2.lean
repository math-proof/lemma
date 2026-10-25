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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section7
open ExactSequence


namespace HomologyCrossProduct

/-- **Theorem 7.2 (Homology cross product).** Bundle packaging the existence
of a natural, bilinear, and normalized homology cross product
`× : H_p(X) × H_q(Y) → H_{p+q}(X × Y)` for singular homology. It supplies a
chain-level cross product `chainCross`, an integer-indexed chain complex
`singularIntComplex X` for each space, a `GradedBilinearMap` packaging the
Leibniz formula and boundary conditions for the chain cross product, and the
induced homology pairing `homologyCross` shown equal to the descent provided
by Lemma 7.1 (`homologyCross_eq_lemma71`), together with the naturality and
normalization properties inherited from the chain-level cross product. -/
structure HomologyCrossProductSingular where
  chainCross : AlgebraicTopologyI.CrossProduct
  singularIntComplex : ∀ (X : Type) [TopologicalSpace X], ExactSequence.IntChainComplex
  gradedBilinear : ∀ (X : Type) (Y : Type) [TopologicalSpace X] [TopologicalSpace Y],
    GradedBilinearMap
      (singularIntComplex X)
      (singularIntComplex Y)
      (singularIntComplex (X × Y))
  homologyCross : ∀ (p q : ℤ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y],
    (singularIntComplex X).homologyGroup p →+
      ((singularIntComplex Y).homologyGroup q →+
        (singularIntComplex (X × Y)).homologyGroup (p + q))
  homologyCross_eq_lemma71 : ∀ (p q : ℤ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y],
    homologyCross p q X Y =
      (gradedBilinear X Y).homology_cross_product p q
  naturality : ∀ (p q : ℕ) (X X' Y Y' : Type)
    [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y'))
    (a : AlgebraicTopologyI.SingularChains p X)
    (b : AlgebraicTopologyI.SingularChains q Y),
    (chainCross.crossMap p q X' Y')
      (AlgebraicTopologyI.SingularChains.map f a)
      (AlgebraicTopologyI.SingularChains.map g b) =
    AlgebraicTopologyI.SingularChains.map
      (ContinuousMap.prodMap f g)
      ((chainCross.crossMap p q X Y) a b)
  normalization_left : ∀ (q : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (b : AlgebraicTopologyI.SingularChains q Y),
    AlgebraicTopologyI.SingularChains.castIdx (show 0 + q = q by omega)
      ((chainCross.crossMap 0 q X Y) (AlgebraicTopologyI.constChain x) b) =
    AlgebraicTopologyI.SingularChains.map (AlgebraicTopologyI.inclusionRight x) b
  normalization_right : ∀ (p : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (y : Y) (a : AlgebraicTopologyI.SingularChains p X),
    (chainCross.crossMap p 0 X Y) a (AlgebraicTopologyI.constChain y) =
    AlgebraicTopologyI.SingularChains.map (AlgebraicTopologyI.inclusionLeft y) a

end HomologyCrossProduct
