/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointMirrorOrbitBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthBoundaryWinding.Part4
import Def.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part2


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

structure HexEndpointBoundaryCore
    {V : Type*} [DecidableEq V]
    (R : HexFiniteRegion) (h0 : ℤ) (D : HexDomain V)
    (P : D.InteriorPairing) where
  interior_sub : P.interior ⊆ D.incidences
  obs_eq : ∀ z, D.obs z =
    endpointParafObservable R.inRegion R.start h0 z (5 / 8) hexChi
  start_value : D.obs R.start = 1


structure HexEndpointMirrorOrbitData
    {I K V : Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K] [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (C : HexEndpointBoundaryCore R h0 D P) where
  heading : V → Fin 3 → ℤ
  hgeom : ∀ v j,
    D.mid v j - D.pos v = (1 / 2 : ℂ) * hexUnit (heading v j)
  startIncidence : HexIncidence V
  start_mid : D.mid startIncidence.vtx startIncidence.edge = R.start
  start_heading : heading startIncidence.vtx startIncidence.edge = 4
  pairs : I → HexMirrorBoundaryPair D heading
  fixed : K → HexFixedBoundaryPoint D heading
  boundary_partition :
    D.incidences \ P.interior =
      {startIncidence} ∪ Finset.univ.biUnion (fun o : I ⊕ K =>
        match o with
        | .inl i => (pairs i).piece
        | .inr k => (fixed k).piece)
  start_orbits_disjoint :
    Disjoint ({startIncidence} : Finset (HexIncidence V))
      (Finset.univ.biUnion (fun o : I ⊕ K =>
        match o with
        | .inl i => (pairs i).piece
        | .inr k => (fixed k).piece))
  orbits_disjoint :
    ((Finset.univ : Finset (I ⊕ K)) : Set (I ⊕ K)).PairwiseDisjoint
      (fun o => match o with
        | .inl i => (pairs i).piece
        | .inr k => (fixed k).piece)

end
end StatMech.Universality
