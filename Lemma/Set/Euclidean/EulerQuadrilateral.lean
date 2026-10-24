import Mathlib
import sympy.Basic


/--
[MetaMathlibExt.euler_quadrilateral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/EulerQuadrilateral.lean)
-/
@[path]
lemma MetaMathlibExt.euler_quadrilateral
  {A B C D : EuclideanSpace ℝ (Fin 2)} :
-- imply
  dist A B ^ 2 + dist B C ^ 2 + dist C D ^ 2 + dist D A ^ 2 =
      dist A C ^ 2 + dist B D ^ 2 +
        4 * dist ((2 : ℝ)⁻¹ • (A + C)) ((2 : ℝ)⁻¹ • (B + D)) ^ 2 := by
-- proof
  have e : ∀ p q : EuclideanSpace ℝ (Fin 2), dist p q ^ 2 = inner ℝ (p - q) (p - q) := fun p q => by
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  rw [e A B, e B C, e C D, e D A, e A C, e B D,
    e ((2 : ℝ)⁻¹ • (A + C)) ((2 : ℝ)⁻¹ • (B + D))]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  rw [real_inner_comm A B, real_inner_comm A C, real_inner_comm B C,
    real_inner_comm A D, real_inner_comm B D, real_inner_comm C D]
  ring


-- created on 2026-10-20
-- updated on 2026-10-23
