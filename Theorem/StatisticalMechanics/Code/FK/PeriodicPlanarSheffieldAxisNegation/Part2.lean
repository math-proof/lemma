/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisNegation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldNearBoundary
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisNegation.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

@[simp] theorem PeriodicPlaneEmbedding.axisNeg_vertexCoord
    (E : PeriodicPlaneEmbedding P) (x : V) (i : Fin 2) :
    E.axisNeg.vertexCoord x i = -E.vertexCoord x i := by
  simp [PeriodicPlaneEmbedding.vertexCoord, PeriodicPlaneEmbedding.axisNeg]

theorem PeriodicGraph.axisNeg_isTranslationInvariant
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) :
    P.axisNeg.IsTranslationInvariant mu := by
  intro z
  simpa [PeriodicGraph.axisNeg, PeriodicGraph.configTranslate] using
    hTI (siteNeg z)

theorem PeriodicGraph.axisNeg_orbitBox (P : PeriodicGraph V) (n : Nat) :
    P.axisNeg.orbitBox n = P.orbitBox n := by
  ext v
  rw [P.axisNeg.mem_orbitBox_iff, P.mem_orbitBox_iff]
  constructor
  · rintro ⟨z, hz, u, hu, rfl⟩
    refine ⟨-z, ?_, u, hu, rfl⟩
    rw [Lattice.mem_box] at hz ⊢
    intro i
    simpa using hz i
  · rintro ⟨z, hz, u, hu, rfl⟩
    refine ⟨-z, ?_, u, hu, ?_⟩
    · rw [Lattice.mem_box] at hz ⊢
      intro i
      simpa using hz i
    · simp [PeriodicGraph.axisNeg, siteNeg]

theorem PeriodicPlaneEmbedding.axisNeg_rectVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) :
    E.axisNeg.rectVertices a b c d = E.rectVertices (-b) (-a) (-d) (-c) := by
  ext x
  change (a ≤ -E.vertexCoord x 0 ∧ -E.vertexCoord x 0 ≤ b ∧
    c ≤ -E.vertexCoord x 1 ∧ -E.vertexCoord x 1 ≤ d) ↔
    (-b ≤ E.vertexCoord x 0 ∧ E.vertexCoord x 0 ≤ -a ∧
      -d ≤ E.vertexCoord x 1 ∧ E.vertexCoord x 1 ≤ -c)
  constructor <;> rintro ⟨h0, h1, h2, h3⟩ <;>
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem PeriodicPlaneEmbedding.axisNeg_leftBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) :
    E.axisNeg.rectLeftBoundaryVertices a b c d =
      E.rectRightBoundaryVertices (-b) (-a) (-d) (-c) := by
  ext x
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    refine ⟨by simpa only [E.axisNeg_rectVertices] using hx,
      y, hxy, ?_⟩
    change -E.vertexCoord y 0 < a at hy
    linarith
  · rintro ⟨hx, y, hxy, hy⟩
    refine ⟨by simpa only [E.axisNeg_rectVertices] using hx,
      y, hxy, ?_⟩
    change -E.vertexCoord y 0 < a
    linarith

theorem PeriodicPlaneEmbedding.axisNeg_leftBoundaryEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (S : Set V) :
    E.axisNeg.rectSideConnectionEvent a b c d S
        (E.axisNeg.rectLeftBoundaryVertices a b c d) =
      E.rectSideConnectionEvent (-b) (-a) (-d) (-c) S
        (E.rectRightBoundaryVertices (-b) (-a) (-d) (-c)) := by
  change P.infiniteSetConnectionWithin
      (E.axisNeg.rectVertices a b c d) S
        (E.axisNeg.rectLeftBoundaryVertices a b c d) = _
  rw [E.axisNeg_rectVertices, E.axisNeg_leftBoundaryVertices]
  rfl


theorem PeriodicPlaneEmbedding.exists_rightBoundaryPlacement_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) :
    ∃ source : Nat → Finset V, ∃ radius : Nat → Nat,
      (∀ N, (source N : Set V) ⊆
        E.rectVertices (-(r + radius N)) (-r)
          (-(radius N : Real)) (radius N)) ∧
      Tendsto (fun N => mu.real
        (E.rectSideConnectionEvent (-(r + radius N)) (-r)
          (-(radius N : Real)) (radius N) (source N : Set V)
          (E.rectRightBoundaryVertices (-(r + radius N)) (-r)
            (-(radius N : Real)) (radius N)))) atTop (nhds 1) := by
  have huniqueNeg :
      mu {omega | P.axisNeg.HasUniqueInfiniteCluster omega} = 1 := by
    simpa [PeriodicGraph.axisNeg] using hunique
  obtain ⟨source, radius, hsource, hlimit⟩ :=
    E.axisNeg.exists_leftBoundaryPlacement_tendsto_one
      mu hFKG (P.axisNeg_isTranslationInvariant mu hTI) huniqueNeg r
  refine ⟨source, radius, ?_, ?_⟩
  · intro N
    simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices,
      E.axisNeg_rectVertices] using hsource N
  · simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent,
      E.axisNeg_leftBoundaryEvent] using hlimit


theorem PeriodicPlaneEmbedding.exists_translatedOrbitBox_rightBoundaryPlacement_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) :
    ∃ base : Nat → Site 2, ∃ radius : Nat → Nat,
      (∀ N, (P.shift (base N) '' (P.orbitBox N : Set V)) ⊆
        E.rectVertices (-(r + radius N)) (-r)
          (-(radius N : Real)) (radius N)) ∧
      Tendsto (fun N => mu.real
        (E.rectSideConnectionEvent (-(r + radius N)) (-r)
          (-(radius N : Real)) (radius N)
          (P.shift (base N) '' (P.orbitBox N : Set V))
          (E.rectRightBoundaryVertices (-(r + radius N)) (-r)
            (-(radius N : Real)) (radius N)))) atTop (nhds 1) := by
  have huniqueNeg :
      mu {omega | P.axisNeg.HasUniqueInfiniteCluster omega} = 1 := by
    simpa [PeriodicGraph.axisNeg] using hunique
  obtain ⟨base, radius, hsource, hlimit⟩ :=
    E.axisNeg.exists_translatedOrbitBox_leftBoundaryPlacement_tendsto_one
      mu hFKG (P.axisNeg_isTranslationInvariant mu hTI) huniqueNeg r
  let base' : Nat → Site 2 := fun N => siteNeg (base N)
  have hset (N : Nat) :
      P.axisNeg.shift (base N) '' (P.axisNeg.orbitBox N : Set V) =
        P.shift (base' N) '' (P.orbitBox N : Set V) := by
    simp only [P.axisNeg_orbitBox]
    rfl
  refine ⟨base', radius, ?_, ?_⟩
  · intro N
    rw [← hset N]
    simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices,
      E.axisNeg_rectVertices] using hsource N
  · simpa only [← hset,
      PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent,
      E.axisNeg_leftBoundaryEvent, neg_neg] using hlimit


theorem PeriodicPlaneEmbedding.exists_buffered_rightBoundaryPlacement_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (buffer : Nat → Nat) (hbuffer : ∀ N, N ≤ buffer N) (r : Real) :
    ∃ base : Nat → Site 2, ∃ radius : Nat → Nat,
      (∀ N, (P.shift (base N) '' (P.orbitBox (buffer N) : Set V)) ⊆
        E.rectVertices (-(r + radius N)) (-r)
          (-(radius N : Real)) (radius N)) ∧
      Tendsto (fun N => mu.real
        (E.rectSideConnectionEvent (-(r + radius N)) (-r)
          (-(radius N : Real)) (radius N)
          (P.shift (base N) '' (P.orbitBox N : Set V))
          (E.rectRightBoundaryVertices (-(r + radius N)) (-r)
            (-(radius N : Real)) (radius N)))) atTop (nhds 1) := by
  have huniqueNeg :
      mu {omega | P.axisNeg.HasUniqueInfiniteCluster omega} = 1 := by
    simpa [PeriodicGraph.axisNeg] using hunique
  obtain ⟨base, radius, hsource, hlimit⟩ :=
    E.axisNeg.exists_buffered_leftBoundaryPlacement_tendsto_one
      mu hFKG (P.axisNeg_isTranslationInvariant mu hTI) huniqueNeg
        buffer hbuffer r
  let base' : Nat → Site 2 := fun N => siteNeg (base N)
  have hset (N k : Nat) :
      P.axisNeg.shift (base N) '' (P.axisNeg.orbitBox k : Set V) =
        P.shift (base' N) '' (P.orbitBox k : Set V) := by
    simp only [P.axisNeg_orbitBox]
    rfl
  refine ⟨base', radius, ?_, ?_⟩
  · intro N
    rw [← hset N (buffer N)]
    simpa [PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices,
      E.axisNeg_rectVertices] using hsource N
  · simpa only [← hset,
      PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent,
      E.axisNeg_leftBoundaryEvent, neg_neg] using hlimit

end StatMech.FK.PeriodicPlanar
