/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairingMaps.Part4
import Def.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part4


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


theorem hexConcrete_vertex_relation (a : ℂ) (h0 : ℤ)
    (hclosure : ∀ W : HexWalk,
      (∀ m ∈ W.mids, m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ)) →
      ∀ x ∈ W.vertices,
        x ∈ ({hexConcreteV0 a h0, hexConcreteVq a h0, hexConcreteVr a h0} : Finset ℂ)) :
    ((hexConcreteV a h0 + hexConcreteDu a h0) - hexConcreteV a h0)
        * parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0
            (hexConcreteV a h0 + hexConcreteDu a h0) (5/8) hexChi
      + ((hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) - hexConcreteV a h0)
          * parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0
              (hexConcreteV a h0 + hexOmega * hexConcreteDu a h0) (5/8) hexChi
      + ((hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) - hexConcreteV a h0)
          * parafObservable (hexConcrete_region a h0 hclosure).inRegion a h0
              (hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0) (5/8) hexChi = 0 :=
  hexClass_vertex_relation (hexConcrete_classification a h0 hclosure) (hexConcreteDu_ne a h0)
    (hexConcrete_summable a h0 hclosure _)
    (hexConcrete_summable a h0 hclosure _)
    (hexConcrete_summable a h0 hclosure _)

end StatMech.Universality
