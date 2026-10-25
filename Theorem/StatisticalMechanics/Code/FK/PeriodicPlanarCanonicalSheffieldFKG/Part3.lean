/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalSheffieldFKG.Part3
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]


theorem PeriodicPlaneEmbedding.finiteRectTargetConnection_isIncreasing
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (a b c d : Real) (x : V) (T : Set V) :
    IsIncreasing (E.finiteRectTargetConnection a b c d x T) := by
  intro eta theta hle
  rintro ⟨x', y, hxx, hy, hreach⟩
  refine ⟨x', y, hxx, hy, hreach.mono ?_⟩
  intro u v huv
  rw [FK.openSub_adj] at huv ⊢
  exact ⟨huv.1, Bool.eq_true_of_true_le (by simpa [huv.2] using hle s(u, v))⟩

theorem PeriodicPlaneEmbedding.rectTargetConnectionEvent_isClopen
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (a b c d : Real) (x : V) (T : Set V) :
    IsClopen (E.rectTargetConnectionEvent a b c d x T) :=
  IsClopen.preimage (isClopen_discrete _)
    (E.continuous_rectRestrict a b c d)

theorem PeriodicPlaneEmbedding.rectTargetConnectionEvent_isIncreasing
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (a b c d : Real) (x : V) (T : Set V) :
    IsIncreasing (E.rectTargetConnectionEvent a b c d x T) := by
  intro omega eta hle homega
  exact E.finiteRectTargetConnection_isIncreasing a b c d x T
    (E.rectRestrict_mono a b c d hle) homega


theorem PeriodicPlaneEmbedding.mem_rectTargetConnectionEvent_iff
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (a b c d : Real) (x : V) (T : Set V)
    (omega : ConfigSpace (Sym2 V)) :
    omega ∈ E.rectTargetConnectionEvent a b c d x T ↔
      ∃ y ∈ T, omega ∈
        P.connectedWithinSet (E.rectVertices a b c d) x y := by
  constructor
  · rintro ⟨x', y, hxx, hy, hreach⟩
    subst x
    rw [E.openSub_rectRestrict_eq_induce] at hreach
    obtain ⟨p⟩ := hreach
    let inclusion :
        (P.openSubgraph omega).induce (E.rectVertices a b c d) →g
          P.openSubgraph omega :=
      { toFun := Subtype.val
        map_rel' := fun huv => huv }
    let q := p.map inclusion
    have hq : ∀ v ∈ q.support, v ∈ E.rectVertices a b c d := by
      intro v hv
      dsimp only [q] at hv
      rw [SimpleGraph.Walk.support_map] at hv
      obtain ⟨u, hu, huv⟩ := List.mem_map.mp hv
      subst v
      exact u.2
    refine ⟨y.1, hy, ?_⟩
    simpa only [inclusion] using P.mem_connectedWithinSet_of_walk q hq
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨q, hq⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxy
    have hx : x ∈ E.rectVertices a b c d := hq x q.start_mem_support
    have hyRect : y ∈ E.rectVertices a b c d := hq y q.end_mem_support
    have hreach :
        (FK.openSub (E.rectGraph a b c d)
          (E.rectRestrict a b c d omega)).Reachable
            ⟨x, hx⟩ ⟨y, hyRect⟩ := by
      rw [E.openSub_rectRestrict_eq_induce]
      exact ⟨q.induce (E.rectVertices a b c d) hq⟩
    exact ⟨⟨x, hx⟩, ⟨y, hyRect⟩, rfl, hy, hreach⟩


theorem PeriodicPlaneEmbedding.rectSideConnectionEvent_eq_finiteWitnessInfinite
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (a b c d : Real) (S : Finset V) (T : Set V) :
    E.rectSideConnectionEvent a b c d (S : Set V) T =
      P.finiteWitnessInfiniteEvent S
        (fun x => E.rectTargetConnectionEvent a b c d x T) := by
  ext omega
  constructor
  · rintro ⟨x, hx, hxinf, y, hy, hxy⟩
    exact Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨hx,
      ⟨(E.mem_rectTargetConnectionEvent_iff a b c d x T omega).2
        ⟨y, hy, hxy⟩, hxinf⟩⟩⟩
  · simp only [PeriodicGraph.finiteWitnessInfiniteEvent, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_setOf_eq]
    rintro ⟨x, hx, hxT, hxinf⟩
    obtain ⟨y, hy, hxy⟩ :=
      (E.mem_rectTargetConnectionEvent_iff a b c d x T omega).1 hxT
    exact ⟨x, hx, hxinf, y, hy, hxy⟩


theorem PeriodicPlaneEmbedding.freeBufferedInfiniteVolume_fkg_rectSideConnection
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (a b c d : Real)
    (S T : Finset V) (sideS sideT : Set V) :
    let mu := (P.freeBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (E.rectSideConnectionEvent a b c d (S : Set V) sideS) *
        mu.real (E.rectSideConnectionEvent a b c d (T : Set V) sideT) <=
      mu.real (E.rectSideConnectionEvent a b c d (S : Set V) sideS ∩
        E.rectSideConnectionEvent a b c d (T : Set V) sideT) := by
  let Q := fun x => E.rectTargetConnectionEvent a b c d x sideS
  let R := fun x => E.rectTargetConnectionEvent a b c d x sideT
  have hfkg := P.freeBufferedInfiniteVolume_fkg_finiteWitnessInfinite
    hp hp1 hq S T Q R
    (fun x _ => E.rectTargetConnectionEvent_isClopen a b c d x sideS)
    (fun x _ => E.rectTargetConnectionEvent_isClopen a b c d x sideT)
    (fun x _ => E.rectTargetConnectionEvent_isIncreasing a b c d x sideS)
    (fun x _ => E.rectTargetConnectionEvent_isIncreasing a b c d x sideT)
  rw [← E.rectSideConnectionEvent_eq_finiteWitnessInfinite
        a b c d S sideS,
      ← E.rectSideConnectionEvent_eq_finiteWitnessInfinite
        a b c d T sideT] at hfkg
  exact hfkg


theorem PeriodicPlaneEmbedding.wiredBufferedInfiniteVolume_fkg_rectSideConnection
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (a b c d : Real)
    (S T : Finset V) (sideS sideT : Set V) :
    let mu := (P.wiredBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (E.rectSideConnectionEvent a b c d (S : Set V) sideS) *
        mu.real (E.rectSideConnectionEvent a b c d (T : Set V) sideT) <=
      mu.real (E.rectSideConnectionEvent a b c d (S : Set V) sideS ∩
        E.rectSideConnectionEvent a b c d (T : Set V) sideT) := by
  let Q := fun x => E.rectTargetConnectionEvent a b c d x sideS
  let R := fun x => E.rectTargetConnectionEvent a b c d x sideT
  have hfkg := P.wiredBufferedInfiniteVolume_fkg_finiteWitnessInfinite
    hp hp1 hq S T Q R
    (fun x _ => E.rectTargetConnectionEvent_isClopen a b c d x sideS)
    (fun x _ => E.rectTargetConnectionEvent_isClopen a b c d x sideT)
    (fun x _ => E.rectTargetConnectionEvent_isIncreasing a b c d x sideS)
    (fun x _ => E.rectTargetConnectionEvent_isIncreasing a b c d x sideT)
  rw [← E.rectSideConnectionEvent_eq_finiteWitnessInfinite
        a b c d S sideS,
      ← E.rectSideConnectionEvent_eq_finiteWitnessInfinite
        a b c d T sideT] at hfkg
  exact hfkg

end StatMech.FK.PeriodicPlanar
