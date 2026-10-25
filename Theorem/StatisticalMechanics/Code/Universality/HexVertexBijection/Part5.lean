/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexBijection.Part3


namespace StatMech.Universality

open Complex

open Function

open HexWalk


variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem relation_emptyRegion (a : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0) :
    ((v + du) - v) * parafObservable (fun _ => False) a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v)
          * parafObservable (fun _ => False) a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable (fun _ => False) a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 :=
  relation_of_partitionFacts (emptyEnumeration a h0 v du) hdu
    (summable_emptyRegion a h0 _ _ _) (summable_emptyRegion a h0 _ _ _)
    (summable_emptyRegion a h0 _ _ _)
    (fun T1 _ _ => absurd T1.2 (Finset.notMem_empty _))
    (fun P1 _ _ => absurd P1.2 (Finset.notMem_empty _))
    (fun P1 _ _ => absurd P1.2 (Finset.notMem_empty _))
    (fun P _ => absurd P.2 (Finset.notMem_empty _))
    (fun P _ => absurd P.2 (Finset.notMem_empty _))
    (fun ts hts _ => absurd (combinedSummand_emptyRegion a h0 v du ts) hts)
    (fun ts hts _ => absurd (combinedSummand_emptyRegion a h0 v du ts) hts)
    (fun ts hts _ => absurd (combinedSummand_emptyRegion a h0 v du ts) hts)

end StatMech.Universality
