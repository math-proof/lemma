import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutMultiplicitySum.Part2
open MvPolynomial


/--
[homogQuotPiece_ideal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutMultiplicitySum.lean)
-/
@[path]
lemma homogQuotPiece_ideal_eq
  {k : Type*}
  [Field k]
  {I J : Ideal (MvPolynomial (Fin 3) k)}
  {n : ℕ}
-- given
  (h : I = J) :
-- imply
  Module.finrank k (homogQuotPiece k I n) = Module.finrank k (homogQuotPiece k J n) := by
-- proof
  subst h; rfl

/--
[bezout_theorem_multiplicity_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutMultiplicitySum.lean)
-/
@[path]
lemma bezout_theorem_multiplicity_sum
  {k : Type*}
  [Field k]
  {d e : ℕ}
  {f g : MvPolynomial (Fin 3) k}
-- given
  (hd : 0 < d)
  (he : 0 < e)
  (hf_homog : f.IsHomogeneous d)
  (hg_homog : g.IsHomogeneous e)
  (hf_ne : f ≠ 0)
  (hg_ne : g ≠ 0)
  (hcoprime : IsCoprime f g) :
-- imply
  ∀ n, d + e - 2 ≤ n → projectiveIntersectionNumber k f g n = d * e := by
-- proof
  intro n hn
  exact bezout_theorem k d e hd he f g hf_homog hg_homog hf_ne hg_ne hcoprime n hn

/--
[projectiveIntersectionNumber_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutMultiplicitySum.lean)
-/
@[path]
lemma projectiveIntersectionNumber_comm
  {k : Type*}
  [Field k]
  {f g : MvPolynomial (Fin 3) k}
  {n : ℕ} :
-- imply
  projectiveIntersectionNumber k f g n = projectiveIntersectionNumber k g f n := by
-- proof
  unfold projectiveIntersectionNumber
  have h : Ideal.span {f} ⊔ Ideal.span {g} = Ideal.span {g} ⊔ Ideal.span {f} := by
    rw [sup_comm]
  exact homogQuotPiece_ideal_eq k h n

/--
[bezout_line_line](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutMultiplicitySum.lean)
-/
@[path]
lemma bezout_line_line
  {k : Type*}
  [Field k]
  {f g : MvPolynomial (Fin 3) k}
  {n : ℕ}
-- given
  (hf : f.IsHomogeneous 1)
  (hg : g.IsHomogeneous 1)
  (hf_ne : f ≠ 0)
  (hg_ne : g ≠ 0)
  (hcop : IsCoprime f g) :
-- imply
  projectiveIntersectionNumber k f g n = 1 := by
-- proof
  have := bezout_theorem_multiplicity_sum k 1 1 one_pos one_pos f g
    hf hg hf_ne hg_ne hcop n (by omega)
  simp at this
  exact this

/--
[bezout_line_conic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutMultiplicitySum.lean)
-/
@[path]
lemma bezout_line_conic
  {k : Type*}
  [Field k]
  {f g : MvPolynomial (Fin 3) k}
  {n : ℕ}
-- given
  (hf : f.IsHomogeneous 1)
  (hg : g.IsHomogeneous 2)
  (hf_ne : f ≠ 0)
  (hg_ne : g ≠ 0)
  (hcop : IsCoprime f g)
  (hn : 1 ≤ n) :
-- imply
  projectiveIntersectionNumber k f g n = 2 := by
-- proof
  have := bezout_theorem_multiplicity_sum k 1 2 one_pos (by norm_num) f g
    hf hg hf_ne hg_ne hcop n (by omega)
  simpa using this

/--
[bezout_conic_conic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutMultiplicitySum.lean)
-/
@[path]
lemma bezout_conic_conic
  {k : Type*}
  [Field k]
  {f g : MvPolynomial (Fin 3) k}
  {n : ℕ}
-- given
  (hf : f.IsHomogeneous 2)
  (hg : g.IsHomogeneous 2)
  (hf_ne : f ≠ 0)
  (hg_ne : g ≠ 0)
  (hcop : IsCoprime f g)
  (hn : 2 ≤ n) :
-- imply
  projectiveIntersectionNumber k f g n = 4 := by
-- proof
  have := bezout_theorem_multiplicity_sum k 2 2 (by norm_num) (by norm_num) f g
    hf hg hf_ne hg_ne hcop n (by omega)
  simpa using this

/--
[bezout_line_cubic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutMultiplicitySum.lean)
-/
@[path]
lemma bezout_line_cubic
  {k : Type*}
  [Field k]
  {f g : MvPolynomial (Fin 3) k}
  {n : ℕ}
-- given
  (hf : f.IsHomogeneous 1)
  (hg : g.IsHomogeneous 3)
  (hf_ne : f ≠ 0)
  (hg_ne : g ≠ 0)
  (hcop : IsCoprime f g)
  (hn : 2 ≤ n) :
-- imply
  projectiveIntersectionNumber k f g n = 3 := by
-- proof
  have := bezout_theorem_multiplicity_sum k 1 3 one_pos (by norm_num) f g
    hf hg hf_ne hg_ne hcop n (by omega)
  simpa using this


-- created on 2026-10-23
