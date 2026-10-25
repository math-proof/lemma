/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorRows.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldOpenBoundaryCrossover
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepConnectorMeasureClosure.Part2
open Filter MeasureTheory Set


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem
    PeriodicPlaneEmbedding.exists_separated_finiteDeepOpenExitedJoinedBoundaryArmEvent_measureReal_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {r R : Real} (hrR : r ≤ R) (s : Real) (t : Int) (N : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ L U : Finset V, ∃ width : Nat,
      (L : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      (U : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      U = L.image (P.shift (verticalShift (1 + t))) ∧
      1 - 2 * Real.sqrt
          (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) -
          3 * epsilon <
        mu.real (E.finiteDeepOpenExitedJoinedBoundaryArmEvent
          r R s (s + t) width L U) := by
  obtain ⟨z₀, width, hSdeep, _hSsepDeep, hmerge⟩ :=
    E.exists_inward_separated_stripPlacement_with_margin
      mu hTI hunique (r := R) (R := R) le_rfl t
        (P.orbitBox N) hepsilon
  let S := (P.orbitBox N).image (P.shift z₀)
  let Ssep := S.image (P.shift (verticalShift (1 + t)))
  obtain ⟨z, hlower, hupper⟩ :=
    E.exists_separated_infiniteOpenBoundaryRays_measureReal_ge
      mu hFKG hTI r s t (S : Set V) hepsilon
  let L := S.image (P.shift (verticalShift z))
  let U := Ssep.image (P.shift (verticalShift z))
  have hU : U = L.image (P.shift (verticalShift (1 + t))) := by
    ext y
    simp only [U, L, Ssep, Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨P.shift (verticalShift z) u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add, ← P.shift_add, add_comm]
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨P.shift (verticalShift (1 + t)) u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add, ← P.shift_add, add_comm]
  have hLdeep : (L : Set V) ⊆ E.rightHalfPlaneVertices R := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    exact (E.shift_mem_rightHalfPlaneVertices_vertical z R u).mpr
      (hSdeep hu)
  have hUdeep : (U : Set V) ⊆ E.rightHalfPlaneVertices R := by
    rw [hU]
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    exact (E.shift_mem_rightHalfPlaneVertices_vertical (1 + t) R u).mpr
      (hLdeep hu)
  have hmerge' : mu.real
      (E.halfPlaneStripPairMergeErrorUnion R width L U) < epsilon := by
    have hv := E.halfPlaneStripPairMergeErrorUnion_measureReal_vertical
      mu hTI z R width S Ssep
    change mu.real (E.halfPlaneStripPairMergeErrorUnion R width
      (S.image (P.shift (verticalShift z)))
      (Ssep.image (P.shift (verticalShift z)))) < epsilon
    rw [hv]
    exact hmerge
  obtain ⟨zLeft, hzLeft⟩ :=
    E.exists_shift_orbitBox_subset_leftComplement N r
  let zOutside := zLeft - z₀
  have hSinside : (S : Set V) ⊆ E.rightHalfPlaneVertices r := by
    intro x hx
    exact hrR.trans (hSdeep hx)
  have hSoutside : P.shift zOutside '' (S : Set V) ⊆
      (E.rightHalfPlaneVertices r)ᶜ := by
    rintro _ ⟨w, hwS, rfl⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hwS
    have hshift : P.shift zOutside (P.shift z₀ v) = P.shift zLeft v := by
      rw [← P.shift_add]
      simp [zOutside]
    rw [hshift]
    exact hzLeft v hv
  have hfull :=
    E.infiniteOpenBoundaryConnection_measureReal_ge_sq_of_translate
      mu hFKG hTI hunique r (S : Set V) zOutside hSinside hSoutside
  have hmass : mu.real (P.setHitsInfinite (S : Set V)) =
      mu.real (P.orbitBoxHitsInfinite N) := by
    dsimp only [S]
    rw [Finset.coe_image,
      P.setHitsInfinite_translate_measureReal_eq mu hTI z₀]
    rfl
  rw [hmass] at hfull
  have hsqrt : Real.sqrt
      (1 - mu.real (E.infiniteOpenBoundaryConnection r (S : Set V))) ≤
      Real.sqrt (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) := by
    apply Real.sqrt_le_sqrt
    linarith
  have hlower' : 1 - Real.sqrt
      (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) - epsilon ≤
      mu.real (E.infiniteOpenBoundaryConnectionTo r (L : Set V)
        (E.lowerBoundaryRayVertices r s)) := by
    have hsource : 1 - Real.sqrt
          (1 - mu.real (E.infiniteOpenBoundaryConnection r (S : Set V))) -
          epsilon ≤
        mu.real (E.infiniteOpenBoundaryConnectionTo r (L : Set V)
          (E.lowerBoundaryRayVertices r s)) := by
      simpa only [L, Finset.coe_image] using hlower
    linarith
  have hupper' : 1 - Real.sqrt
      (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) - epsilon ≤
      mu.real (E.infiniteOpenBoundaryConnectionTo r (U : Set V)
        (E.upperBoundaryRayVertices r (s + t))) := by
    have hsource : 1 - Real.sqrt
          (1 - mu.real (E.infiniteOpenBoundaryConnection r (S : Set V))) -
          epsilon ≤
        mu.real (E.infiniteOpenBoundaryConnectionTo r (U : Set V)
          (E.upperBoundaryRayVertices r (s + t))) := by
      have himage : P.shift (verticalShift (1 + t)) ''
          (P.shift (verticalShift z) '' (S : Set V)) =
          P.shift (verticalShift (z + 1 + t)) '' (S : Set V) := by
        rw [P.shift_image_vertical_add]
        congr 3
        ring_nf
      rw [hU]
      simpa only [L, Finset.coe_image, himage] using hupper
    linarith
  refine ⟨L, U, width, hLdeep, hUdeep, hU, ?_⟩
  have hbound :=
    E.finiteDeepOpenExitedJoinedBoundaryArmEvent_measureReal_ge
      mu r R s (s + t) width L U
  linarith

end StatMech.FK.PeriodicPlanar
