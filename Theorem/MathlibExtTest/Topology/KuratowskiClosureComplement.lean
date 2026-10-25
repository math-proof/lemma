/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/KuratowskiClosureComplement.lean -/

import Lemma.Set.KuratowskiClosureComplement
import Instance.MathlibExtTest.Topology.KuratowskiClosureComplement
open Set
open Topology.ClosureCompl
open MathlibExt.Topology.KuratowskiClosureComplement


/-- Mathlib's canonical obtainability predicate contains its seed set. -/
example : IsObtainable ({0} : Set (Fin 2)) {0} :=
  .base

/-- The canonical predicate is closed under complement. -/
example : IsObtainable ({0} : Set (Fin 2)) ({0}ᶜ) :=
  .complement .base

/-- The canonical predicate is closed under closure. -/
example : IsObtainable ({0} : Set (Fin 2)) (closure {0}) :=
  .closure .base

/-- The canonical fourteen forms characterize obtainability. -/
example : ({0} : Set (Fin 2)) ∈ theFourteen {0} ↔
    IsObtainable ({0} : Set (Fin 2)) {0} :=
  mem_theFourteen_iff_isObtainable

/-- Mathlib's direct numerical bound is available. -/
example : {t : Set (Fin 2) | IsObtainable ({0} : Set (Fin 2)) t}.ncard ≤ 14 :=
  ncard_isObtainable_le_fourteen _

/-- The finite-and-cardinality wrapper holds on a concrete space and set. -/
example : {t : Set (Fin 2) | IsObtainable ({0} : Set (Fin 2)) t}.Finite ∧
    {t : Set (Fin 2) | IsObtainable ({0} : Set (Fin 2)) t}.ncard ≤ 14 :=
  kuratowski_closure_complement _

