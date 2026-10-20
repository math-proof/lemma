/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/KuratowskiClosureComplement.lean -/

import Archive.Kuratowski

open Set

namespace MathlibExt.Topology.KuratowskiClosureComplement

variable {X : Type*} [TopologicalSpace X]

/--
The closure-complement orbit of any set contains at most 14 distinct sets.

This packages Mathlib's canonical `Topology.ClosureCompl.IsObtainable` interface
as the finite-and-cardinality form requested by the original Wanted entry.

Source: Casimir Kuratowski, "Sur l'opération Ā de l'Analysis Situs,"
*Fundamenta Mathematicae* 3 (1922), 182–199, DOI 10.4064/FM-3-1-182-199.
-/
theorem kuratowski_closure_complement (s : Set X) :
    {t : Set X | Topology.ClosureCompl.IsObtainable s t}.Finite ∧
      {t : Set X | Topology.ClosureCompl.IsObtainable s t}.ncard ≤ 14 := by
  have hset : {t : Set X | Topology.ClosureCompl.IsObtainable s t} =
      ↑(Topology.ClosureCompl.theFourteen s).toFinset := by
    ext t
    change Topology.ClosureCompl.IsObtainable s t ↔
      t ∈ (Topology.ClosureCompl.theFourteen s).toFinset
    rw [Multiset.mem_toFinset,
      Topology.ClosureCompl.mem_theFourteen_iff_isObtainable]
  constructor
  · rw [hset]
    exact Finset.finite_toSet _
  · exact Topology.ClosureCompl.ncard_isObtainable_le_fourteen s

end MathlibExt.Topology.KuratowskiClosureComplement
