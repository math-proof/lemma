/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Mathlib.Topology.Constructions
import Mathlib.Topology.UnitInterval
import Def.v1.Atlas.AlgebraicTopologyI.code.Section6
open Finset BigOperators


namespace AlgebraicTopologyI

/-- (Theorem 6.2) Bundle of data and axioms for the singular cross product
`× : S_p(X) × S_q(Y) → S_{p+q}(X × Y)`: it is natural in both arguments, bilinear,
satisfies the Leibniz rule `d(a × b) = (da) × b + (-1)^p a × db`, and is normalized so
that `c_x^0 × b = (j_x)_* b` and `a × c_y^0 = (i_y)_* a`. -/
structure CrossProduct where
  crossMap : ∀ (p q : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y],
    SingularChains p X →+ (SingularChains q Y →+ SingularChains (p + q) (X × Y))
  naturality : ∀ (p q : ℕ) (X X' Y Y' : Type)
    [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y'))
    (a : SingularChains p X) (b : SingularChains q Y),
    (crossMap p q X' Y') (SingularChains.map f a) (SingularChains.map g b) =
      SingularChains.map (ContinuousMap.prodMap f g) ((crossMap p q X Y) a b)
  leibniz : ∀ (p q : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularChains (p + 1) X) (b : SingularChains (q + 1) Y),
    let ab := (crossMap (p + 1) (q + 1) X Y) a b
    let ab' := SingularChains.castIdx (show (p + 1) + (q + 1) = (p + q + 1) + 1 by omega) ab
    let dab := boundaryMap (p + q + 1) (X × Y) ab'
    let da_b := SingularChains.castIdx (show p + (q + 1) = p + q + 1 by rfl)
                  ((crossMap p (q + 1) X Y) (boundaryMap p X a) b)
    let a_db := SingularChains.castIdx (show (p + 1) + q = p + q + 1 by omega)
                  ((crossMap (p + 1) q X Y) a (boundaryMap q Y b))
    dab = da_b + (-1 : ℤ) ^ (p + 1) • a_db
  normalization_left : ∀ (q : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (b : SingularChains q Y),
    SingularChains.castIdx (show 0 + q = q by omega)
      ((crossMap 0 q X Y) (constChain x) b) =
      SingularChains.map (inclusionRight x) b
  normalization_right : ∀ (p : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (y : Y) (a : SingularChains p X),
    (crossMap p 0 X Y) a (constChain y) =
      SingularChains.map (inclusionLeft y) a

end AlgebraicTopologyI
