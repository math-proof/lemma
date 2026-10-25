/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/Group/OpenProfiniteCompletion.lean -/

import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Def.Topology.Algebra.Group.OpenProfiniteCompletion
open CategoryTheory
open scoped Pointwise

universe u

/-!
# Open profinite completion from open finite-index normal subgroups.

Corrects the source formalization: an open subgroup of an arbitrary
topological group need not have finite index. We index by open *and*
finite-index normal subgroups.
-/


namespace ProfiniteGrp.OpenProfiniteCompletion

/-- Continuity of `etaFn`; needs only separate continuity of `*`. -/
theorem etaFn_continuous (G : Type u) [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] : Continuous (etaFn G) := by
  apply continuous_induced_rng.mpr (continuous_pi _)
  intro H
  apply Continuous.mk
  intro s _hs
  let s' : Set (G ⧸ H.1.toSubgroup) := fun x ↦ s x
  change IsOpen ((QuotientGroup.mk' H.1.toSubgroup) ⁻¹' s')
  rw [← (Set.biUnion_preimage_singleton (QuotientGroup.mk' H.1.toSubgroup) s')]
  refine isOpen_iUnion (fun i ↦ isOpen_iUnion (fun _ ↦ ?_))
  convert! IsOpen.leftCoset H.2 (Quotient.out i)
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  conv_lhs => rhs; rw [← QuotientGroup.out_eq' i]
  change (↑x : G ⧸ H.1.toSubgroup) = ↑(Quotient.out i) ↔
    x ∈ Quotient.out i • (↑H.1.toSubgroup : Set G)
  rw [eq_comm, QuotientGroup.eq]
  exact Iff.symm Set.mem_smul_set_iff_inv_smul_mem

end ProfiniteGrp.OpenProfiniteCompletion
