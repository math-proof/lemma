import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999


/--
[AlgebraicCurve_isIntegral_adjoin_map_algHom](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_isIntegral_adjoin_map_algHom.lean)
-/
@[path]
private lemma main
  [CommRing K] [CommRing F] [CommRing F'] [Algebra K F] [Algebra K F']
  (φ : F →ₐ[K] F') {j x : F}
-- given
  (hx : IsIntegral (Algebra.adjoin K {j}) x) :
-- imply
  IsIntegral (Algebra.adjoin K {φ j}) (φ x) := by
-- proof
  have hle : (Algebra.adjoin K {j}).map φ ≤ Algebra.adjoin K {φ j} := by
    rw [Subalgebra.map_le]
    refine Algebra.adjoin_le fun y hy => ?_
    rw [Set.mem_singleton_iff.mp hy]
    show j ∈ Subalgebra.comap φ (Algebra.adjoin K {φ j})
    rw [Subalgebra.mem_comap]
    exact Algebra.subset_adjoin rfl
  have hmem : ∀ a : ↥(Algebra.adjoin K {j}),
      (φ.comp (Algebra.adjoin K {j}).val) a ∈ Algebra.adjoin K {φ j} :=
    fun a => hle (Subalgebra.mem_map.mpr ⟨(a : F), a.2, rfl⟩)
  refine IsIntegral.map_of_comp_eq
    ((φ.comp (Algebra.adjoin K {j}).val).codRestrict (Algebra.adjoin K {φ j}) hmem).toRingHom
    φ.toRingHom ?_ hx
  ext a
  rfl


-- created on 2026-10-20
