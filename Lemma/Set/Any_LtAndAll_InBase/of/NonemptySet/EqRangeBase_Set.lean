import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry TopologicalSpace

/--
[AlgebraicGeometry_exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty.lean)
-/
@[main]
private lemma main
  {X Z : Scheme.{u}}
  {i : Z ⟶ X} [IsClosedImmersion i]
  {T : Closeds X}
  {U : Z.Opens}
-- given
  (hT : Set.range i.base = (T : Set X))
  (hU : (U : Set Z).Nonempty) :
-- imply
  ∃ T' : Closeds X, T' < T ∧ ∀ z : Z, z ∉ U → i.base z ∈ T' := by
-- proof
  have hce : Topology.IsClosedEmbedding i.base := i.isClosedEmbedding
  refine ⟨⟨i.base '' ((U : Set Z)ᶜ), hce.isClosedMap _ U.isOpen.isClosed_compl⟩, ?_, fun z hz => ⟨z, hz, rfl⟩⟩
  rw [SetLike.lt_iff_le_and_exists]
  obtain ⟨u, hu⟩ := hU
  refine ⟨?_, i.base u, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, -, rfl⟩ := (Closeds.mem_mk).mp hx
    have : i.base z ∈ (T : Set X) := hT ▸ ⟨z, rfl⟩
    exact this
  · have : i.base u ∈ (T : Set X) := hT ▸ ⟨u, rfl⟩
    exact this
  · intro h
    obtain ⟨z, hz, hzu⟩ := (Closeds.mem_mk).mp h
    exact hz (by rwa [hce.injective hzu])


-- created on 2026-10-05
