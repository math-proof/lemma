import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.MatrixGroupIntersections
open Matrix CompatibleTriple


namespace CompatibleTriple

/--
[J_mul_left_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MatrixGroupIntersections.lean)
-/
@[path]
lemma J_mul_left_cancel
  {l : Type*}
  [DecidableEq l]
  [Fintype l]
  {l}
  {M N : Matrix (l ⊕ l) (l ⊕ l) ℝ}
-- given
  (h : J l ℝ * M = J l ℝ * N) :
-- imply
  M = N := by
-- proof
  have hJinv : (J l ℝ)⁻¹ * (J l ℝ) = 1 := nonsing_inv_mul _ (isUnit_det_J l ℝ)
  calc M = ((J l ℝ)⁻¹ * J l ℝ) * M := by rw [hJinv, one_mul]
    _ = (J l ℝ)⁻¹ * (J l ℝ * N) := by rw [mul_assoc, ← h, ← mul_assoc]
    _ = N := by rw [← mul_assoc, hJinv, one_mul]

end CompatibleTriple

namespace CompatibleTriple

/--
[comm_J_transpose](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MatrixGroupIntersections.lean)
-/
@[path]
lemma comm_J_transpose
  {l : Type*}
  [DecidableEq l]
  [Fintype l]
  {l}
  {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
-- given
  (h : A * J l ℝ = J l ℝ * A) :
-- imply
  A.transpose * J l ℝ = J l ℝ * A.transpose := by
-- proof
  have h1 : (A * J l ℝ).transpose = (J l ℝ * A).transpose := by rw [h]
  simp [transpose_mul] at h1
  exact neg_injective h1.symm

end CompatibleTriple

namespace CompatibleTriple

/--
[sp_cap_gl_sub_O](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MatrixGroupIntersections.lean)
-/
@[path]
lemma sp_cap_gl_sub_O
  {l : Type*}
  [DecidableEq l]
  [Fintype l]
  {l}
  {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
-- given
  (hSp : A ∈ Sp2n l)
  (hGL : A ∈ GLnC l) :
-- imply
  A ∈ O2n l := by
-- proof
  simp only [Sp2n, GLnC, O2n, Set.mem_setOf_eq] at *
  apply J_mul_left_cancel
  rw [mul_one]
  have hcomm_t := comm_J_transpose hGL
  calc J l ℝ * (A.transpose * A)
    = (J l ℝ * A.transpose) * A := by rw [mul_assoc]
    _ = (A.transpose * J l ℝ) * A := by rw [hcomm_t]
    _ = A.transpose * J l ℝ * A := by rw [mul_assoc]
    _ = J l ℝ := hSp

end CompatibleTriple

namespace CompatibleTriple

/--
[O_cap_gl_sub_Sp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MatrixGroupIntersections.lean)
-/
@[path]
lemma O_cap_gl_sub_Sp
  {l : Type*}
  [DecidableEq l]
  [Fintype l]
  {l}
  {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
-- given
  (hO : A ∈ O2n l)
  (hGL : A ∈ GLnC l) :
-- imply
  A ∈ Sp2n l := by
-- proof
  simp only [Sp2n, GLnC, O2n, Set.mem_setOf_eq] at *
  calc A.transpose * J l ℝ * A
    = A.transpose * (J l ℝ * A) := by rw [mul_assoc]
    _ = A.transpose * (A * J l ℝ) := by rw [hGL]
    _ = (A.transpose * A) * J l ℝ := by rw [mul_assoc]
    _ = 1 * J l ℝ := by rw [hO]
    _ = J l ℝ := by rw [one_mul]

end CompatibleTriple

namespace CompatibleTriple

/--
[sp_cap_O_sub_GL](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MatrixGroupIntersections.lean)
-/
@[path]
lemma sp_cap_O_sub_GL
  {l : Type*}
  [DecidableEq l]
  [Fintype l]
  {l}
  {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
-- given
  (hSp : A ∈ Sp2n l)
  (hO : A ∈ O2n l) :
-- imply
  A ∈ GLnC l := by
-- proof
  simp only [Sp2n, GLnC, O2n, Set.mem_setOf_eq] at *
  have hO' : A * A.transpose = 1 := mul_eq_one_comm.mp hO
  have h : A * (A.transpose * J l ℝ * A) = J l ℝ * A := by
    calc A * (A.transpose * J l ℝ * A)
      = A * A.transpose * J l ℝ * A := by simp [Matrix.mul_assoc]
      _ = 1 * J l ℝ * A := by rw [hO']
      _ = J l ℝ * A := by rw [one_mul]
  rwa [hSp] at h

end CompatibleTriple

namespace CompatibleTriple

/--
[sp_cap_O_eq_U](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MatrixGroupIntersections.lean)
-/
@[path]
lemma sp_cap_O_eq_U
  {l : Type*}
  [DecidableEq l]
  [Fintype l]
  {l} :
-- imply
  Sp2n l ∩ O2n l = Un l := by
-- proof
  ext A
  simp only [Set.mem_inter_iff, Un]
  constructor
  · intro ⟨hSp, hO⟩
    exact ⟨sp_cap_O_sub_GL hSp hO, hO⟩
  · intro ⟨hGL, hO⟩
    exact ⟨O_cap_gl_sub_Sp hO hGL, hO⟩

end CompatibleTriple


-- created on 2026-10-23
