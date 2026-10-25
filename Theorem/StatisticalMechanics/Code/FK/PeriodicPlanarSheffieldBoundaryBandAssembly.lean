/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandPadding.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldExclusion
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepTemplateGridAssembly
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicPlaneEmbedding.exists_translatedFamily_leftBoundaryExhaustion_centered
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (S : Finset V) (shift : ι → Site 2)
    (hinside : ∀ i,
      P.shift (shift i) '' (S : Set V) ⊆ E.rightHalfPlaneVertices r)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat, ∀ i,
      P.shift (shift i) '' (S : Set V) ⊆
          E.rectVertices r (r + radius)
            ((shift i 1 : Real) - radius) ((shift i 1 : Real) + radius) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent r (r + radius)
          ((shift i 1 : Real) - radius) ((shift i 1 : Real) + radius)
          (P.shift (shift i) '' (S : Set V))
          (E.rectLeftBoundaryVertices r (r + radius)
            ((shift i 1 : Real) - radius)
            ((shift i 1 : Real) + radius))) := by
  let normalized : ι → Site 2 := fun i =>
    shift i + verticalShift (-(shift i 1))
  have hnormalized (i : ι) :
      P.shift (normalized i) '' (S : Set V) =
        P.shift (verticalShift (-(shift i 1))) ''
          (P.shift (shift i) '' (S : Set V)) := by
    rw [P.shift_image_shift]
  have hinsideNormalized (i : ι) :
      P.shift (normalized i) '' (S : Set V) ⊆
        E.rightHalfPlaneVertices r := by
    rw [hnormalized]
    exact E.shift_image_rightHalfPlaneVertices_vertical
      (-(shift i 1)) r ▸ Set.image_mono (hinside i)
  obtain ⟨radius, hradius⟩ :=
    E.exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique r S normalized hinsideNormalized hepsilon
  refine ⟨radius, ?_⟩
  intro i
  let z := verticalShift (shift i 1)
  have hz0 : (z 0 : Real) = 0 := by simp [z, verticalShift]
  have hz1 : (z 1 : Real) = shift i 1 := by simp [z, verticalShift]
  have horiginal :
      P.shift z '' (P.shift (normalized i) '' (S : Set V)) =
        P.shift (shift i) '' (S : Set V) := by
    rw [P.shift_image_shift]
    apply congrArg (fun w : Site 2 => P.shift w '' (S : Set V))
    dsimp only [normalized, z]
    funext k
    fin_cases k <;> simp [verticalShift]
  constructor
  · intro x hx
    rw [← horiginal] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z r (r + radius)
      (-(radius : Real)) radius y).2 ((hradius i).1 hy)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have htranslate := E.rectLeftConnection_translate_measureReal_eq
      mu hTI z r (r + radius) (-(radius : Real)) radius
      (P.shift (normalized i) '' (S : Set V))
    rw [hz0, hz1, horiginal] at htranslate
    have hp := (hradius i).2
    change (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
      mu.real (E.rectSideConnectionEvent r (r + radius)
        (-(radius : Real)) radius
        (P.shift (normalized i) '' (S : Set V))
        (E.rectLeftBoundaryVertices r (r + radius)
          (-(radius : Real)) radius)) at hp
    rw [← htranslate] at hp
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.exists_leftBoundaryExhaustion_uniform_tangentialPlacement
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (S : Finset V) (normal : ι → Site 2)
    (hinside : ∀ i,
      P.shift (normal i) '' (S : Set V) ⊆ E.rightHalfPlaneVertices r)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat, ∀ tangent : ι → Int, ∀ i,
      let shift := normal i + verticalShift (tangent i)
      P.shift shift '' (S : Set V) ⊆
          E.rectVertices r (r + radius)
            ((tangent i : Real) - radius) ((tangent i : Real) + radius) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent r (r + radius)
          ((tangent i : Real) - radius) ((tangent i : Real) + radius)
          (P.shift shift '' (S : Set V))
          (E.rectLeftBoundaryVertices r (r + radius)
            ((tangent i : Real) - radius) ((tangent i : Real) + radius))) := by
  obtain ⟨radius, hradius⟩ :=
    E.exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique r S normal hinside hepsilon
  refine ⟨radius, ?_⟩
  intro tangent i
  dsimp only
  let z := verticalShift (tangent i)
  have hz0 : (z 0 : Real) = 0 := by simp [z]
  have hz1 : (z 1 : Real) = tangent i := by simp [z]
  have himage :
      P.shift z '' (P.shift (normal i) '' (S : Set V)) =
        P.shift (normal i + verticalShift (tangent i)) '' (S : Set V) := by
    rw [P.shift_image_shift]
  constructor
  · intro x hx
    rw [← himage] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z r (r + radius)
      (-(radius : Real)) radius y).2 ((hradius i).1 hy)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have htranslate := E.rectLeftConnection_translate_measureReal_eq
      mu hTI z r (r + radius) (-(radius : Real)) radius
      (P.shift (normal i) '' (S : Set V))
    rw [hz0, hz1, himage] at htranslate
    have hp := (hradius i).2
    change (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
      mu.real (E.rectSideConnectionEvent r (r + radius)
        (-(radius : Real)) radius (P.shift (normal i) '' (S : Set V))
        (E.rectLeftBoundaryVertices r (r + radius)
          (-(radius : Real)) radius)) at hp
    rw [← htranslate] at hp
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.exists_translatedFamily_rightBoundaryExhaustion_centered
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (S : Finset V) (shift : ι → Site 2)
    (hinside : ∀ i, P.shift (shift i) '' (S : Set V) ⊆
      {v | E.vertexCoord v 0 ≤ -r})
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat, ∀ i,
      P.shift (shift i) '' (S : Set V) ⊆
          E.rectVertices (-(r + radius)) (-r)
            ((shift i 1 : Real) - radius) ((shift i 1 : Real) + radius) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent (-(r + radius)) (-r)
          ((shift i 1 : Real) - radius) ((shift i 1 : Real) + radius)
          (P.shift (shift i) '' (S : Set V))
          (E.rectRightBoundaryVertices (-(r + radius)) (-r)
            ((shift i 1 : Real) - radius)
            ((shift i 1 : Real) + radius))) := by
  let normalized : ι → Site 2 := fun i =>
    shift i + verticalShift (-(shift i 1))
  have hnormalized (i : ι) :
      P.shift (normalized i) '' (S : Set V) =
        P.shift (verticalShift (-(shift i 1))) ''
          (P.shift (shift i) '' (S : Set V)) := by
    rw [P.shift_image_shift]
  have hinsideNormalized (i : ι) :
      P.shift (normalized i) '' (S : Set V) ⊆
        {v | E.vertexCoord v 0 ≤ -r} := by
    rw [hnormalized]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h := hinside i hy
    simpa [E.vertexCoord_shift, verticalShift] using h
  obtain ⟨radius, hradius⟩ :=
    E.exists_translatedFamily_rightBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique r S normalized hinsideNormalized hepsilon
  refine ⟨radius, ?_⟩
  intro i
  let z := verticalShift (shift i 1)
  have hz0 : (z 0 : Real) = 0 := by simp [z]
  have hz1 : (z 1 : Real) = shift i 1 := by simp [z]
  have horiginal :
      P.shift z '' (P.shift (normalized i) '' (S : Set V)) =
        P.shift (shift i) '' (S : Set V) := by
    rw [P.shift_image_shift]
    apply congrArg (fun w : Site 2 => P.shift w '' (S : Set V))
    dsimp only [normalized, z]
    funext k
    fin_cases k <;> simp [verticalShift]
  constructor
  · intro x hx
    rw [← horiginal] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(r + radius)) (-r)
      (-(radius : Real)) radius y).2 ((hradius i).1 hy)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have htranslate := E.rectRightConnection_translate_measureReal_eq
      mu hTI z (-(r + radius)) (-r) (-(radius : Real)) radius
      (P.shift (normalized i) '' (S : Set V))
    rw [hz0, hz1, horiginal] at htranslate
    have hp := (hradius i).2
    rw [← htranslate] at hp
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.exists_translatedFamily_bottomBoundaryExhaustion_centered
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (S : Finset V) (shift : ι → Site 2)
    (hinside : ∀ i, P.shift (shift i) '' (S : Set V) ⊆
      {v | r ≤ E.vertexCoord v 1})
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat, ∀ i,
      P.shift (shift i) '' (S : Set V) ⊆
          E.rectVertices ((shift i 0 : Real) - radius)
            ((shift i 0 : Real) + radius) r (r + radius) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent
          ((shift i 0 : Real) - radius) ((shift i 0 : Real) + radius)
          r (r + radius) (P.shift (shift i) '' (S : Set V))
          (E.rectBottomBoundaryVertices
            ((shift i 0 : Real) - radius) ((shift i 0 : Real) + radius)
            r (r + radius))) := by
  let normalized : ι → Site 2 := fun i =>
    shift i + horizontalShift (-(shift i 0))
  have hnormalized (i : ι) :
      P.shift (normalized i) '' (S : Set V) =
        P.shift (horizontalShift (-(shift i 0))) ''
          (P.shift (shift i) '' (S : Set V)) := by
    rw [P.shift_image_shift]
  have hinsideNormalized (i : ι) :
      P.shift (normalized i) '' (S : Set V) ⊆
        {v | r ≤ E.vertexCoord v 1} := by
    rw [hnormalized]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h := hinside i hy
    simpa [E.vertexCoord_shift, horizontalShift] using h
  obtain ⟨radius, hradius⟩ :=
    E.exists_translatedFamily_bottomBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique r S normalized hinsideNormalized hepsilon
  refine ⟨radius, ?_⟩
  intro i
  let z := horizontalShift (shift i 0)
  have hz0 : (z 0 : Real) = shift i 0 := by simp [z]
  have hz1 : (z 1 : Real) = 0 := by simp [z]
  have horiginal :
      P.shift z '' (P.shift (normalized i) '' (S : Set V)) =
        P.shift (shift i) '' (S : Set V) := by
    rw [P.shift_image_shift]
    apply congrArg (fun w : Site 2 => P.shift w '' (S : Set V))
    dsimp only [normalized, z]
    funext k
    fin_cases k <;> simp [horizontalShift]
  constructor
  · intro x hx
    rw [← horiginal] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(radius : Real)) radius
      r (r + radius) y).2 ((hradius i).1 hy)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have htranslate := E.rectBottomConnection_translate_measureReal_eq
      mu hTI z (-(radius : Real)) radius r (r + radius)
      (P.shift (normalized i) '' (S : Set V))
    rw [hz0, hz1, horiginal] at htranslate
    have hp := (hradius i).2
    rw [← htranslate] at hp
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.exists_translatedFamily_topBoundaryExhaustion_centered
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (S : Finset V) (shift : ι → Site 2)
    (hinside : ∀ i, P.shift (shift i) '' (S : Set V) ⊆
      {v | E.vertexCoord v 1 ≤ -r})
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat, ∀ i,
      P.shift (shift i) '' (S : Set V) ⊆
          E.rectVertices ((shift i 0 : Real) - radius)
            ((shift i 0 : Real) + radius) (-(r + radius)) (-r) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent
          ((shift i 0 : Real) - radius) ((shift i 0 : Real) + radius)
          (-(r + radius)) (-r) (P.shift (shift i) '' (S : Set V))
          (E.rectTopBoundaryVertices
            ((shift i 0 : Real) - radius) ((shift i 0 : Real) + radius)
            (-(r + radius)) (-r))) := by
  let normalized : ι → Site 2 := fun i =>
    shift i + horizontalShift (-(shift i 0))
  have hnormalized (i : ι) :
      P.shift (normalized i) '' (S : Set V) =
        P.shift (horizontalShift (-(shift i 0))) ''
          (P.shift (shift i) '' (S : Set V)) := by
    rw [P.shift_image_shift]
  have hinsideNormalized (i : ι) :
      P.shift (normalized i) '' (S : Set V) ⊆
        {v | E.vertexCoord v 1 ≤ -r} := by
    rw [hnormalized]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h := hinside i hy
    simpa [E.vertexCoord_shift, horizontalShift] using h
  obtain ⟨radius, hradius⟩ :=
    E.exists_translatedFamily_topBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique r S normalized hinsideNormalized hepsilon
  refine ⟨radius, ?_⟩
  intro i
  let z := horizontalShift (shift i 0)
  have hz0 : (z 0 : Real) = shift i 0 := by simp [z]
  have hz1 : (z 1 : Real) = 0 := by simp [z]
  have horiginal :
      P.shift z '' (P.shift (normalized i) '' (S : Set V)) =
        P.shift (shift i) '' (S : Set V) := by
    rw [P.shift_image_shift]
    apply congrArg (fun w : Site 2 => P.shift w '' (S : Set V))
    dsimp only [normalized, z]
    funext k
    fin_cases k <;> simp [horizontalShift]
  constructor
  · intro x hx
    rw [← horiginal] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(radius : Real)) radius
      (-(r + radius)) (-r) y).2 ((hradius i).1 hy)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have htranslate := E.rectTopConnection_translate_measureReal_eq
      mu hTI z (-(radius : Real)) radius (-(r + radius)) (-r)
      (P.shift (normalized i) '' (S : Set V))
    rw [hz0, hz1, horiginal] at htranslate
    have hp := (hradius i).2
    rw [← htranslate] at hp
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.exists_rightBoundaryExhaustion_uniform_tangentialPlacement
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (S : Finset V) (normal : ι → Site 2)
    (hinside : ∀ i, P.shift (normal i) '' (S : Set V) ⊆
      {v | E.vertexCoord v 0 ≤ -r})
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat, ∀ tangent : ι → Int, ∀ i,
      let shift := normal i + verticalShift (tangent i)
      P.shift shift '' (S : Set V) ⊆
          E.rectVertices (-(r + radius)) (-r)
            ((tangent i : Real) - radius) ((tangent i : Real) + radius) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent (-(r + radius)) (-r)
          ((tangent i : Real) - radius) ((tangent i : Real) + radius)
          (P.shift shift '' (S : Set V))
          (E.rectRightBoundaryVertices (-(r + radius)) (-r)
            ((tangent i : Real) - radius) ((tangent i : Real) + radius))) := by
  obtain ⟨radius, hradius⟩ :=
    E.exists_translatedFamily_rightBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique r S normal hinside hepsilon
  refine ⟨radius, ?_⟩
  intro tangent i
  dsimp only
  let z := verticalShift (tangent i)
  have hz0 : (z 0 : Real) = 0 := by simp [z]
  have hz1 : (z 1 : Real) = tangent i := by simp [z]
  have himage : P.shift z '' (P.shift (normal i) '' (S : Set V)) =
      P.shift (normal i + verticalShift (tangent i)) '' (S : Set V) := by
    rw [P.shift_image_shift]
  constructor
  · rintro x hx
    rw [← himage] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(r + radius)) (-r)
      (-(radius : Real)) radius y).2 ((hradius i).1 hy)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have ht := E.rectRightConnection_translate_measureReal_eq mu hTI z
      (-(r + radius)) (-r) (-(radius : Real)) radius
      (P.shift (normal i) '' (S : Set V))
    rw [hz0, hz1, himage] at ht
    have hp := (hradius i).2
    rw [← ht] at hp
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.exists_bottomBoundaryExhaustion_uniform_tangentialPlacement
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (S : Finset V) (normal : ι → Site 2)
    (hinside : ∀ i, P.shift (normal i) '' (S : Set V) ⊆
      {v | r ≤ E.vertexCoord v 1})
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat, ∀ tangent : ι → Int, ∀ i,
      let shift := normal i + horizontalShift (tangent i)
      P.shift shift '' (S : Set V) ⊆
          E.rectVertices ((tangent i : Real) - radius)
            ((tangent i : Real) + radius) r (r + radius) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent
          ((tangent i : Real) - radius) ((tangent i : Real) + radius)
          r (r + radius) (P.shift shift '' (S : Set V))
          (E.rectBottomBoundaryVertices
            ((tangent i : Real) - radius) ((tangent i : Real) + radius)
            r (r + radius))) := by
  obtain ⟨radius, hradius⟩ :=
    E.exists_translatedFamily_bottomBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique r S normal hinside hepsilon
  refine ⟨radius, ?_⟩
  intro tangent i
  dsimp only
  let z := horizontalShift (tangent i)
  have hz0 : (z 0 : Real) = tangent i := by simp [z]
  have hz1 : (z 1 : Real) = 0 := by simp [z]
  have himage : P.shift z '' (P.shift (normal i) '' (S : Set V)) =
      P.shift (normal i + horizontalShift (tangent i)) '' (S : Set V) := by
    rw [P.shift_image_shift]
  constructor
  · rintro x hx
    rw [← himage] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(radius : Real)) radius
      r (r + radius) y).2 ((hradius i).1 hy)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have ht := E.rectBottomConnection_translate_measureReal_eq mu hTI z
      (-(radius : Real)) radius r (r + radius)
      (P.shift (normal i) '' (S : Set V))
    rw [hz0, hz1, himage] at ht
    have hp := (hradius i).2
    rw [← ht] at hp
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hp


theorem PeriodicPlaneEmbedding.exists_topBoundaryExhaustion_uniform_tangentialPlacement
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Real) (S : Finset V) (normal : ι → Site 2)
    (hinside : ∀ i, P.shift (normal i) '' (S : Set V) ⊆
      {v | E.vertexCoord v 1 ≤ -r})
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius : Nat, ∀ tangent : ι → Int, ∀ i,
      let shift := normal i + horizontalShift (tangent i)
      P.shift shift '' (S : Set V) ⊆
          E.rectVertices ((tangent i : Real) - radius)
            ((tangent i : Real) + radius) (-(r + radius)) (-r) ∧
      (mu.real (P.setHitsInfinite (S : Set V))) ^ 2 - epsilon <
        mu.real (E.rectSideConnectionEvent
          ((tangent i : Real) - radius) ((tangent i : Real) + radius)
          (-(r + radius)) (-r) (P.shift shift '' (S : Set V))
          (E.rectTopBoundaryVertices
            ((tangent i : Real) - radius) ((tangent i : Real) + radius)
            (-(r + radius)) (-r))) := by
  obtain ⟨radius, hradius⟩ :=
    E.exists_translatedFamily_topBoundaryExhaustion_measureReal_gt
      mu hFKG hTI hunique r S normal hinside hepsilon
  refine ⟨radius, ?_⟩
  intro tangent i
  dsimp only
  let z := horizontalShift (tangent i)
  have hz0 : (z 0 : Real) = tangent i := by simp [z]
  have hz1 : (z 1 : Real) = 0 := by simp [z]
  have himage : P.shift z '' (P.shift (normal i) '' (S : Set V)) =
      P.shift (normal i + horizontalShift (tangent i)) '' (S : Set V) := by
    rw [P.shift_image_shift]
  constructor
  · rintro x hx
    rw [← himage] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem := (E.shift_mem_rectVertices z (-(radius : Real)) radius
      (-(r + radius)) (-r) y).2 ((hradius i).1 hy)
    rw [hz0, hz1] at hmem
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hmem
  · have ht := E.rectTopConnection_translate_measureReal_eq mu hTI z
      (-(radius : Real)) radius (-(r + radius)) (-r)
      (P.shift (normal i) '' (S : Set V))
    rw [hz0, hz1, himage] at ht
    have hp := (hradius i).2
    rw [← ht] at hp
    simpa only [add_zero, sub_eq_add_neg, add_comm] using hp


end StatMech.FK.PeriodicPlanar
