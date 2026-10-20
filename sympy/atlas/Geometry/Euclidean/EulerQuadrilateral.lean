/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/EulerQuadrilateral.lean -/

import Mathlib.Analysis.InnerProductSpace.PiL2

/-- Euler's quadrilateral theorem (statement `euler-quadrilateral-s1` from
https://en.wikipedia.org/wiki/Euler%27s_quadrilateral_theorem): a quadrilateral
with sides `a`, `b`, `c`, `d`, diagonals `e`, `f`, and segment `m` joining the
diagonal midpoints satisfies `a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = e ^ 2 + f ^ 2 + 4 * m ^ 2`.
Lengths are Euclidean `dist` and midpoints are averages.
Proves `Wanted` entry `MetaMathlibExt.euler_quadrilateral`.
-/
theorem MetaMathlibExt.euler_quadrilateral {A B C D : EuclideanSpace ℝ (Fin 2)} :
    dist A B ^ 2 + dist B C ^ 2 + dist C D ^ 2 + dist D A ^ 2 =
      dist A C ^ 2 + dist B D ^ 2 +
        4 * dist ((2 : ℝ)⁻¹ • (A + C)) ((2 : ℝ)⁻¹ • (B + D)) ^ 2 := by
  have e : ∀ p q : EuclideanSpace ℝ (Fin 2), dist p q ^ 2 = inner ℝ (p - q) (p - q) := fun p q => by
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  rw [e A B, e B C, e C D, e D A, e A C, e B D,
    e ((2 : ℝ)⁻¹ • (A + C)) ((2 : ℝ)⁻¹ • (B + D))]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  rw [real_inner_comm A B, real_inner_comm A C, real_inner_comm B C,
    real_inner_comm A D, real_inner_comm B D, real_inner_comm C D]
  ring
