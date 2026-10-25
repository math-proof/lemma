import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Reflection.ReflectionGroupsCoxeter
open Set HyperplaneArrangement
open scoped InnerProductSpace


namespace HyperplaneArrangement

/--
[simplyTransitive_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/ReflectionGroupsCoxeter.lean)
-/
@[path]
private lemma simplyTransitive_theorem
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {arr : HyperplaneArrangement E} [CoxeterArrangement arr] :
-- imply
  arr.SimplyTransitive := by
-- proof
  intro C D
  obtain ⟨w, hw⟩ := CoxeterArrangement.transitive_on_chambers (arr := arr) C D
  refine ⟨w, hw, ?_⟩
  intro w' hw'
  have h_fix : w'⁻¹ * w = ⟨1, one_mem _⟩ := by
    apply CoxeterArrangement.faithful_on_chambers C
    show imageByIsometry (↑(w'⁻¹ * w)) C.set = C.set
    ext x; simp only [imageByIsometry, Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hwy : (↑w : AffineIsometryEquiv ℝ E E) y ∈ D.set := by rw [← hw]; exact ⟨y, hy, rfl⟩
      have : (↑w' : AffineIsometryEquiv ℝ E E).symm ((↑w : AffineIsometryEquiv ℝ E E) y) ∈ C.set := by
        rw [← hw'] at hwy; obtain ⟨z, hz, hze⟩ := hwy
        rw [show (↑w' : AffineIsometryEquiv ℝ E E).symm ((↑w : AffineIsometryEquiv ℝ E E) y) =
          (↑w' : AffineIsometryEquiv ℝ E E).symm ((↑w' : AffineIsometryEquiv ℝ E E) z) from by rw [hze]]
        simp [AffineIsometryEquiv.symm_apply_apply]; exact hz
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using this
    · intro hx
      refine ⟨(↑w : AffineIsometryEquiv ℝ E E).symm ((↑w' : AffineIsometryEquiv ℝ E E) x), ?_, ?_⟩
      · have hw'x : (↑w' : AffineIsometryEquiv ℝ E E) x ∈ D.set := by rw [← hw']; exact ⟨x, hx, rfl⟩
        rw [← hw] at hw'x; obtain ⟨z, hz, hze⟩ := hw'x
        rw [show (↑w : AffineIsometryEquiv ℝ E E).symm ((↑w' : AffineIsometryEquiv ℝ E E) x) =
          (↑w : AffineIsometryEquiv ℝ E E).symm ((↑w : AffineIsometryEquiv ℝ E E) z) from by rw [hze]]
        simp [AffineIsometryEquiv.symm_apply_apply]; exact hz
      · show (↑(w'⁻¹ * w) : AffineIsometryEquiv ℝ E E) ((↑w : AffineIsometryEquiv ℝ E E).symm ((↑w' : AffineIsometryEquiv ℝ E E) x)) = x
        simp [Subgroup.coe_mul]
  have : w = w' := by
    have h1 := congr_arg Subtype.val h_fix
    simp [Subgroup.coe_mul] at h1
    ext1
    calc (w : AffineIsometryEquiv ℝ E E) = (↑w' * (↑w')⁻¹) * ↑w := by simp
      _ = ↑w' * ((↑w')⁻¹ * ↑w) := by rw [mul_assoc]
      _ = ↑w' * 1 := by rw [h1]
      _ = ↑w' := by rw [mul_one]
  exact this.symm

end HyperplaneArrangement

namespace HyperplaneArrangement

/--
[fundamentalDomain_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/ReflectionGroupsCoxeter.lean)
-/
@[path]
private lemma fundamentalDomain_theorem
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {arr : HyperplaneArrangement E} [CoxeterArrangement arr]
  {C : arr.Chamber} :
-- imply
  arr.FundamentalDomain C := by
-- proof
  constructor
  · intro x; exact CoxeterArrangement.closure_covers C x
  · intro w₁ w₂ hw; exact CoxeterArrangement.open_chambers_disjoint C w₁ w₂ hw

end HyperplaneArrangement


-- created on 2026-10-23
-- updated on 2026-10-24
