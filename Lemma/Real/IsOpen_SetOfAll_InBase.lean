import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_isOpen_setOf_forall_preimage_mem_of_universallyClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isOpen_setOf_forall_preimage_mem_of_universallyClosed.lean)
-/
@[path]
private lemma main
  {Z T Y : Scheme.{u}}
  {π : Z ⟶ T} [UniversallyClosed π]
  {φ : Z ⟶ Y}
  {V : Y.Opens} :
-- imply
  IsOpen {t : T | ∀ z : Z, π.base z = t → φ.base z ∈ V} := by
-- proof
  have hset : {t : T | ∀ z : Z, π.base z = t → φ.base z ∈ V} = (π.base '' ((φ.base ⁻¹' (V : Set Y))ᶜ))ᶜ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_image, Set.mem_preimage, not_exists, not_and, SetLike.mem_coe]
    constructor
    · intro h z hz hzt; exact hz (h z hzt)
    · intro h z hzt; by_contra hz; exact h z hz hzt
  rw [hset, isOpen_compl_iff]
  refine π.isClosedMap _ ?_
  exact (V.isOpen.preimage φ.continuous).isClosed_compl


-- created on 2026-10-05
