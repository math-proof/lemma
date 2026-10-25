-- Carved from Lemma/Definitions/Def_RepTheory_GL2CongruenceSubgroup.lean: instance decls only.
import Mathlib
import Lemma.RepTheory.GL2CongruenceSubgroup

set_option autoImplicit false

open scoped Topology

namespace FLT.SmoothVectors


section NeighbourhoodBasis

variable (p : ℕ) [Fact p.Prime]

instance nonarchimedeanGroup_gl2Padic : NonarchimedeanGroup (GL (Fin 2) ℚ_[p]) where
  is_nonarchimedean := by
    intro U hU
    obtain ⟨n, hn⟩ := exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one p hU
    exact ⟨⟨gl2CongruenceSubgroup p n, isOpen_coe_gl2CongruenceSubgroup p n⟩, hn⟩

end NeighbourhoodBasis

end FLT.SmoothVectors
