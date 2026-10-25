import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaTagEquiv
open Finset StatMech StatMech.Ising


/--
[lpReplicaCurrentCopies_transportTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaTagEquiv.lean)
-/
@[path]
private lemma lpReplicaCurrentCopies_transportTag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
  {E : Copy (lpReplicaCurrentGraph G sites) m ≃ Copy (lpReplicaCurrentGraph G sites) n}
  {row current : Bool}
-- given
  (sites : I -> V)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaCurrentCopies G sites n (lpReplicaTransportTag G sites E tag) row current = (lpReplicaCurrentCopies G sites m tag row current).map E.toEmbedding := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentCopies_transportTag G sites E tag row current

/--
[lpReplicaRowCopies_transportTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaTagEquiv.lean)
-/
@[path]
private lemma lpReplicaRowCopies_transportTag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
  {E : Copy (lpReplicaCurrentGraph G sites) m ≃ Copy (lpReplicaCurrentGraph G sites) n}
  {row : Bool}
-- given
  (sites : I -> V)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaRowCopies G sites n (lpReplicaTransportTag G sites E tag) row = (lpReplicaRowCopies G sites m tag row).map E.toEmbedding := by
-- proof
  apply StatMech.Ising.lpReplicaRowCopies_transportTag G sites E tag row

/--
[lpReplicaRowGate_transportTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaTagEquiv.lean)
-/
@[path]
private lemma lpReplicaRowGate_transportTag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
  {E : Copy (lpReplicaCurrentGraph G sites) m ≃ Copy (lpReplicaCurrentGraph G sites) n}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (hends : forall c, endsM (lpReplicaCurrentGraph G sites) n (E c) = endsM (lpReplicaCurrentGraph G sites) m c)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  LPReplicaRowGate G sites n A B (lpReplicaTransportTag G sites E tag) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_transportTag G sites E hends A B tag hgate


-- created on 2026-10-23
