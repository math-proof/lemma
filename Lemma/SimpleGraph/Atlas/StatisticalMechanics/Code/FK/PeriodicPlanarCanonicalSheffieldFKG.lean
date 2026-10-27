import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalSheffieldFKG.Part3
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.bufferedSetBoundaryEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma bufferedSetBoundaryEvent_isIncreasing_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {S : Set V}
  {n : Nat} :
-- imply
  IsIncreasing (P.bufferedSetBoundaryEvent S n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedSetBoundaryEvent_isIncreasing P S n

/--
[PeriodicGraph.bufferedSetBoundaryCylinder_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma bufferedSetBoundaryCylinder_isClopen_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {S : Set V}
  {n : Nat} :
-- imply
  IsClopen (P.bufferedCylinder n (P.bufferedSetBoundaryEvent S n)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedSetBoundaryCylinder_isClopen P S n

/--
[PeriodicGraph.bufferedSetBoundaryCylinder_antitone_from](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma bufferedSetBoundaryCylinder_antitone_from_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {S : Set V}
  {N : Nat}
-- given
  (hS : S ⊆ (P.orbitBox (P.bufferedRadius N) : Set V)) :
-- imply
  Antitone (fun k => P.bufferedCylinder (N + k) (P.bufferedSetBoundaryEvent S (N + k))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedSetBoundaryCylinder_antitone_from P S N hS

/--
[PeriodicGraph.iInter_bufferedSetBoundaryCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma iInter_bufferedSetBoundaryCylinder_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {S : Set V}
  {N : Nat}
-- given
  (hSfinite : S.Finite)
  (hS : S ⊆ (P.orbitBox (P.bufferedRadius N) : Set V)) :
-- imply
  (iInter fun k => P.bufferedCylinder (N + k) (P.bufferedSetBoundaryEvent S (N + k))) = P.setHitsInfinite S := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.iInter_bufferedSetBoundaryCylinder P S hSfinite N hS

/--
[PeriodicGraph.freeBufferedInfiniteVolume_fkg_setHitsInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_fkg_setHitsInfinite_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
  {S T : Finset V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  let mu := (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) mu.real (P.setHitsInfinite (S : Set V)) * mu.real (P.setHitsInfinite (T : Set V)) <= mu.real (P.setHitsInfinite (S : Set V) ∩ P.setHitsInfinite (T : Set V)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_fkg_setHitsInfinite P hp hp1 hq S T

/--
[PeriodicGraph.wiredBufferedInfiniteVolume_fkg_setHitsInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma wiredBufferedInfiniteVolume_fkg_setHitsInfinite_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
  {S T : Finset V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  let mu := (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) mu.real (P.setHitsInfinite (S : Set V)) * mu.real (P.setHitsInfinite (T : Set V)) <= mu.real (P.setHitsInfinite (S : Set V) ∩ P.setHitsInfinite (T : Set V)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedInfiniteVolume_fkg_setHitsInfinite P hp hp1 hq S T

/--
[PeriodicGraph.finiteWitnessBoundaryApprox_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma finiteWitnessBoundaryApprox_isClopen_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {S : Finset V}
  {n : Nat}
-- given
  (Q : V -> Set (ConfigSpace (Sym2 V)))
  (hQ : ∀ x ∈ S, IsClopen (Q x)) :
-- imply
  IsClopen (P.finiteWitnessBoundaryApprox S Q n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.finiteWitnessBoundaryApprox_isClopen P S Q hQ n

/--
[PeriodicGraph.finiteWitnessBoundaryApprox_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma finiteWitnessBoundaryApprox_isIncreasing_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {S : Finset V}
  {n : Nat}
-- given
  (Q : V -> Set (ConfigSpace (Sym2 V)))
  (hQ : ∀ x ∈ S, IsIncreasing (Q x)) :
-- imply
  IsIncreasing (P.finiteWitnessBoundaryApprox S Q n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.finiteWitnessBoundaryApprox_isIncreasing P S Q hQ n

/--
[PeriodicGraph.finiteWitnessBoundaryApprox_antitone_from](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma finiteWitnessBoundaryApprox_antitone_from_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {S : Finset V}
  {N : Nat}
-- given
  (Q : V -> Set (ConfigSpace (Sym2 V)))
  (hS : (S : Set V) ⊆ (P.orbitBox (P.bufferedRadius N) : Set V)) :
-- imply
  Antitone (fun k => P.finiteWitnessBoundaryApprox S Q (N + k)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.finiteWitnessBoundaryApprox_antitone_from P S Q N hS

/--
[PeriodicGraph.iInter_finiteWitnessBoundaryApprox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma iInter_finiteWitnessBoundaryApprox_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {S : Finset V}
  {N : Nat}
-- given
  (Q : V -> Set (ConfigSpace (Sym2 V)))
  (hS : (S : Set V) ⊆ (P.orbitBox (P.bufferedRadius N) : Set V)) :
-- imply
  (iInter fun k => P.finiteWitnessBoundaryApprox S Q (N + k)) = P.finiteWitnessInfiniteEvent S Q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.iInter_finiteWitnessBoundaryApprox P S Q N hS

/--
[PeriodicGraph.freeBufferedInfiniteVolume_fkg_finiteWitnessInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_fkg_finiteWitnessInfinite_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
  {S T : Finset V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (Q R : V -> Set (ConfigSpace (Sym2 V)))
  (hQcl : ∀ x ∈ S, IsClopen (Q x))
  (hRcl : ∀ x ∈ T, IsClopen (R x))
  (hQinc : ∀ x ∈ S, IsIncreasing (Q x))
  (hRinc : ∀ x ∈ T, IsIncreasing (R x)) :
-- imply
  let mu := (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) mu.real (P.finiteWitnessInfiniteEvent S Q) * mu.real (P.finiteWitnessInfiniteEvent T R) <= mu.real (P.finiteWitnessInfiniteEvent S Q ∩ P.finiteWitnessInfiniteEvent T R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_fkg_finiteWitnessInfinite P hp hp1 hq S T Q R hQcl hRcl hQinc hRinc

/--
[PeriodicGraph.wiredBufferedInfiniteVolume_fkg_finiteWitnessInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma wiredBufferedInfiniteVolume_fkg_finiteWitnessInfinite_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {p q : Real}
  {S T : Finset V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (Q R : V -> Set (ConfigSpace (Sym2 V)))
  (hQcl : ∀ x ∈ S, IsClopen (Q x))
  (hRcl : ∀ x ∈ T, IsClopen (R x))
  (hQinc : ∀ x ∈ S, IsIncreasing (Q x))
  (hRinc : ∀ x ∈ T, IsIncreasing (R x)) :
-- imply
  let mu := (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) mu.real (P.finiteWitnessInfiniteEvent S Q) * mu.real (P.finiteWitnessInfiniteEvent T R) <= mu.real (P.finiteWitnessInfiniteEvent S Q ∩ P.finiteWitnessInfiniteEvent T R) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.wiredBufferedInfiniteVolume_fkg_finiteWitnessInfinite P hp hp1 hq S T Q R hQcl hRcl hQinc hRinc

/--
[PeriodicPlaneEmbedding.finiteRectTargetConnection_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma finiteRectTargetConnection_isIncreasing_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {x : V}
  {T : Set V} :
-- imply
  IsIncreasing (E.finiteRectTargetConnection a b c d x T) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteRectTargetConnection_isIncreasing E a b c d x T

/--
[PeriodicPlaneEmbedding.rectTargetConnectionEvent_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma rectTargetConnectionEvent_isClopen_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {x : V}
  {T : Set V} :
-- imply
  IsClopen (E.rectTargetConnectionEvent a b c d x T) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectTargetConnectionEvent_isClopen E a b c d x T

/--
[PeriodicPlaneEmbedding.rectTargetConnectionEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma rectTargetConnectionEvent_isIncreasing_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {x : V}
  {T : Set V} :
-- imply
  IsIncreasing (E.rectTargetConnectionEvent a b c d x T) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectTargetConnectionEvent_isIncreasing E a b c d x T

/--
[PeriodicPlaneEmbedding.mem_rectTargetConnectionEvent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma mem_rectTargetConnectionEvent_iff_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {x : V}
  {T : Set V}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  omega ∈ E.rectTargetConnectionEvent a b c d x T ↔ ∃ y ∈ T, omega ∈ P.connectedWithinSet (E.rectVertices a b c d) x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.mem_rectTargetConnectionEvent_iff E a b c d x T omega

/--
[PeriodicPlaneEmbedding.rectSideConnectionEvent_eq_finiteWitnessInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma rectSideConnectionEvent_eq_finiteWitnessInfinite_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real}
  {S : Finset V}
  {T : Set V} :
-- imply
  E.rectSideConnectionEvent a b c d (S : Set V) T = P.finiteWitnessInfiniteEvent S (fun x => E.rectTargetConnectionEvent a b c d x T) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectSideConnectionEvent_eq_finiteWitnessInfinite E a b c d S T

/--
[PeriodicPlaneEmbedding.freeBufferedInfiniteVolume_fkg_rectSideConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_fkg_rectSideConnection_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {E : PeriodicPlaneEmbedding P}
  {p q : Real}
  {a b c d : Real}
  {S T : Finset V}
  {sideS sideT : Set V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  let mu := (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) mu.real (E.rectSideConnectionEvent a b c d (S : Set V) sideS) * mu.real (E.rectSideConnectionEvent a b c d (T : Set V) sideT) <= mu.real (E.rectSideConnectionEvent a b c d (S : Set V) sideS ∩ E.rectSideConnectionEvent a b c d (T : Set V) sideT) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.freeBufferedInfiniteVolume_fkg_rectSideConnection E hp hp1 hq a b c d S T sideS sideT

/--
[PeriodicPlaneEmbedding.wiredBufferedInfiniteVolume_fkg_rectSideConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean)
-/
@[path]
private lemma wiredBufferedInfiniteVolume_fkg_rectSideConnection_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {E : PeriodicPlaneEmbedding P}
  {p q : Real}
  {a b c d : Real}
  {S T : Finset V}
  {sideS sideT : Set V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  let mu := (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))) mu.real (E.rectSideConnectionEvent a b c d (S : Set V) sideS) * mu.real (E.rectSideConnectionEvent a b c d (T : Set V) sideT) <= mu.real (E.rectSideConnectionEvent a b c d (S : Set V) sideS ∩ E.rectSideConnectionEvent a b c d (T : Set V) sideT) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.wiredBufferedInfiniteVolume_fkg_rectSideConnection E hp hp1 hq a b c d S T sideS sideT


-- created on 2026-10-23
