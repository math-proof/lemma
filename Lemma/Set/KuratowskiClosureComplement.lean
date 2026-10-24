import Mathlib
import sympy.Basic
import Archive.Kuratowski
open Set


namespace MathlibExt.Topology.KuratowskiClosureComplement

/--
[kuratowski_closure_complement](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/KuratowskiClosureComplement.lean)
-/
@[path]
lemma kuratowski_closure_complement
  [TopologicalSpace X]
  {s : Set X} :
-- imply
  {t : Set X | Topology.ClosureCompl.IsObtainable s t}.Finite ∧
      {t : Set X | Topology.ClosureCompl.IsObtainable s t}.ncard ≤ 14 := by
-- proof
  have hset : {t : Set X | Topology.ClosureCompl.IsObtainable s t} =
    ↑(Topology.ClosureCompl.theFourteen s).toFinset := by
    ext t
    change Topology.ClosureCompl.IsObtainable s t ↔
      t ∈ (Topology.ClosureCompl.theFourteen s).toFinset
    rw [Multiset.mem_toFinset,
      Topology.ClosureCompl.mem_theFourteen_iff_isObtainable]
  constructor
  ·
    rw [hset]
    exact Finset.finite_toSet _
  · exact Topology.ClosureCompl.ncard_isObtainable_le_fourteen s

end MathlibExt.Topology.KuratowskiClosureComplement


-- created on 2026-10-20
-- updated on 2026-10-23
