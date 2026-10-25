/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AptThinness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.AptIsCoxeterProof
import Lemma.Set.ApartmentsToApartmentSystem.eq.Apartments.of.IsThick
import Def.v1.Atlas.Buildings.code.Building.AptThinness
open ChamberComplex

variable {V : Type*} [DecidableEq V]


namespace AptIsCoxeterProof

/-- The simplicial complex underlying `aptChamberComplex` is precisely the apartment $A$. -/
theorem aptChamberComplex_eq {K : ChamberComplex V} (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments) :
    (aptChamberComplex pre A hA).toSimplicialComplex = A := by
  simp [aptChamberComplex]

/-- The `aptChamberComplex` associated to an apartment is thin. -/
theorem apt_is_thin {K : ChamberComplex V} (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments) :
    (aptChamberComplex pre A hA).IsThin := by
  obtain ⟨cc, hcc_eq, hthin⟩ := pre.apt_thin_cc A hA


  have heq : (aptChamberComplex pre A hA).toSimplicialComplex =
      cc.toSimplicialComplex := by
    rw [aptChamberComplex_eq, hcc_eq]

  intro F C hFC hCmax

  have hFC' : cc.toSimplicialComplex.IsFacet F C := by
    have := hFC; rw [heq] at this; exact this
  have hCmax' : cc.toSimplicialComplex.IsMaximal C := by
    have := hCmax; rw [heq] at this; exact this
  obtain ⟨D, ⟨hDne, hDfacet, hDmax⟩, hDuniq⟩ := hthin F C hFC' hCmax'
  refine ⟨D, ⟨hDne, ?_, ?_⟩, ?_⟩
  ·
    have := hDfacet; rw [← heq] at this; exact this
  ·
    have := hDmax; rw [← heq] at this; exact this
  ·
    intro D' ⟨hD'ne, hD'facet, hD'max⟩
    apply hDuniq
    refine ⟨hD'ne, ?_, ?_⟩
    · have := hD'facet; rw [heq] at this; exact this
    · have := hD'max; rw [heq] at this; exact this

/-- In a thick chamber complex, every apartment admits an underlying thin chamber complex. -/
theorem apt_thinness_from_thickness
    (K : ChamberComplex V) (_hThick : K.IsThick)
    (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments) :
    ∃ (cc : ChamberComplex V), cc.toSimplicialComplex = A ∧ cc.IsThin :=
  ⟨aptChamberComplex pre A hA,
   aptChamberComplex_eq pre A hA,
   apt_is_thin pre A hA⟩

end AptIsCoxeterProof
