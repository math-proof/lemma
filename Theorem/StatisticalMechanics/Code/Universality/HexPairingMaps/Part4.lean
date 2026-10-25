/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairingMaps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexVertexClassification.Part3
import Def.StatisticalMechanics.Code.Universality.HexPairingMaps.Part3


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem hexPairing_vertex_relation (a w : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0)
    (hclosure : ∀ W : HexWalk, (∀ m ∈ W.mids, m ∈ ({a} : Finset ℂ)) →
      ∀ x ∈ W.vertices, x ∈ ({w} : Finset ℂ))
    (hap : a ≠ v + du) (haq : a ≠ v + hexOmega * du) (har : a ≠ v + hexOmega ^ 2 * du) :
    ((v + du) - v)
        * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v)
          * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable (hexFiniteRegion_single a w hclosure).inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi
      = 0 :=
  hexPairing_emptySupport_vertex_relation a w h0 v du hdu hclosure hap haq har

end StatMech.Universality
