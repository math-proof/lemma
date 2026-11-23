/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AptThinness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.Buildings.code.Building.AptIsCoxeterProof
public import Theorem.Set.ApartmentsToApartmentSystem.eq.Apartments.of.IsThick
public import Theorem.v1.Atlas.Buildings.code.Building.AptThinness

@[expose] public section

open ChamberComplex

variable {V : Type*} [DecidableEq V]


namespace AptIsCoxeterProof

/-- The chamber complex structure on an apartment $A$ inherited from `PreApartmentData`. -/
noncomputable def aptChamberComplex {K : ChamberComplex V} (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments) :
    ChamberComplex V where
  faces := A.faces
  nonempty_of_mem := A.nonempty_of_mem
  down_closed := A.down_closed
  exists_maximal := fun s hs => apt_face_in_chamber pre A hA s hs
  gallery_connected := fun C D hCmax hDmax =>
    apt_gallery_connected pre A hA C D hCmax hDmax

end AptIsCoxeterProof
