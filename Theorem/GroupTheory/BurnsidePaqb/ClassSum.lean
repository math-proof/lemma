/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ClassSum.lean -/

import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Complex.Basic
import Theorem.GroupTheory.BurnsidePaqbReduction.Part2
import Def.GroupTheory.BurnsidePaqb.ClassSum
/-!
Conjugacy-class-algebra stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is the conjugacy-class-algebra stage of the complete Burnside proof,
mechanically ported from the audited source `extracted/Burnside/ClassSum.lean`.
-/


namespace BurnsidePaqb

variable {G : Type*} [Group G] [Fintype G]

/-- Class sums are central in the group algebra. -/
theorem classSum_central (g h : G) :
    classSum (conjClass g) * MonoidAlgebra.of ℂ G h =
      MonoidAlgebra.of ℂ G h * classSum (conjClass g) := by
  simp only [classSum, Finset.sum_mul, Finset.mul_sum, ← map_mul]
  refine Finset.sum_bij (fun x _ => h⁻¹ * x * h) ?_ ?_ ?_ ?_
  · intro x hx
    simpa using conj_mem_conjClass g h⁻¹ x hx
  · intro a₁ _ a₂ _ heq
    have h2 : h * (h⁻¹ * a₁ * h) * h⁻¹ = h * (h⁻¹ * a₂ * h) * h⁻¹ :=
      congrArg (fun y => h * y * h⁻¹) heq
    have e1 : h * (h⁻¹ * a₁ * h) * h⁻¹ = a₁ := by group
    have e2 : h * (h⁻¹ * a₂ * h) * h⁻¹ = a₂ := by group
    rw [e1, e2] at h2
    exact h2
  · intro y hy
    refine ⟨h * y * h⁻¹, conj_mem_conjClass g h y hy, ?_⟩
    show h⁻¹ * (h * y * h⁻¹) * h = y
    group
  · intro x hx
    show MonoidAlgebra.of ℂ G (x * h) = MonoidAlgebra.of ℂ G (h * (h⁻¹ * x * h))
    congr 1
    group

/-- Class sums commute with every group-algebra element. -/
theorem classSum_central' (g : G) (w : MonoidAlgebra ℂ G) :
    w * classSum (conjClass g) = classSum (conjClass g) * w := by
  have hsingle : ∀ m r, MonoidAlgebra.single m r = r • MonoidAlgebra.of ℂ G m := by
    intro m r
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
  induction w using MonoidAlgebra.induction with
  | zero => simp
  | single_add m r x _ _ ih =>
    rw [add_mul, mul_add, ih]
    have h1 : MonoidAlgebra.single m r * classSum (conjClass g)
        = classSum (conjClass g) * MonoidAlgebra.single m r := by
      rw [hsingle m r, smul_mul_assoc, (classSum_central g m).symm,
        ← mul_smul_comm, ← hsingle m r]
    rw [h1]

end BurnsidePaqb
