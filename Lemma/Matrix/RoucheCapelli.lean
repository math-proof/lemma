import Mathlib
import sympy.Basic
open scoped Matrix


namespace MetaMathlibExt

/--
[roucheCapelli_mulVec_mem_span_cols](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/RoucheCapelli.lean)
-/
@[path]
private lemma roucheCapelli_mulVec_mem_span_cols {m n K : Type*} [Fintype n] [Field K]
  (A : Matrix m n K) (x : n → K) :
  A *ᵥ x ∈ Submodule.span K (Set.range A.col) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨x, ?_⟩
  simp only [Matrix.mulVec_eq_sum, Matrix.col, IsCentralScalar.op_smul_eq_smul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[roucheCapelli_solvable_iff_mem_span_cols](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/RoucheCapelli.lean)
-/
@[path]
private lemma roucheCapelli_solvable_iff_mem_span_cols {m n K : Type*} [Fintype n]
  [Field K] (A : Matrix m n K) (b : m → K) :
  (∃ x : n → K, A *ᵥ x = b) ↔ b ∈ Submodule.span K (Set.range A.col) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact roucheCapelli_mulVec_mem_span_cols A x
  · intro hb
    rw [Submodule.mem_span_range_iff_exists_fun] at hb
    obtain ⟨x, hx⟩ := hb
    refine ⟨x, ?_⟩
    simpa only [Matrix.mulVec_eq_sum, Matrix.col, IsCentralScalar.op_smul_eq_smul] using hx

end MetaMathlibExt

namespace MetaMathlibExt

/--
[roucheCapelli_range_augmented_cols](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/RoucheCapelli.lean)
-/
@[path]
private lemma roucheCapelli_range_augmented_cols {m n K : Type*}
  (A : Matrix m n K) (b : m → K) :
  Set.range
    (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
      Matrix m (n ⊕ Fin 1) K).col =
    insert b (Set.range A.col) := by
  have hcol :
    (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
      Matrix m (n ⊕ Fin 1) K).col =
      Sum.elim A.col (fun _ : Fin 1 => b) := by
    funext j i
    cases j <;> rfl
  rw [hcol, Set.Sum.elim_range, Set.range_const, Set.union_singleton]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[roucheCapelli_span_cols_le_augmented](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/RoucheCapelli.lean)
-/
@[path]
private lemma roucheCapelli_span_cols_le_augmented {m n K : Type*} [Field K]
  (A : Matrix m n K) (b : m → K) :
  Submodule.span K (Set.range A.col) ≤
    Submodule.span K
      (Set.range
        (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
          Matrix m (n ⊕ Fin 1) K).col) := by
  rw [roucheCapelli_range_augmented_cols A b]
  exact Submodule.span_mono (Set.subset_insert b (Set.range A.col))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[roucheCapelli_span_augmented_eq_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/RoucheCapelli.lean)
-/
@[path]
private lemma roucheCapelli_span_augmented_eq_of_mem {m n K : Type*} [Field K]
  (A : Matrix m n K) (b : m → K) (hb : b ∈ Submodule.span K (Set.range A.col)) :
  Submodule.span K
    (Set.range
      (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
        Matrix m (n ⊕ Fin 1) K).col) =
    Submodule.span K (Set.range A.col) := by
  rw [roucheCapelli_range_augmented_cols A b]
  exact Submodule.span_insert_eq_span hb

end MetaMathlibExt

namespace MetaMathlibExt

/--
[roucheCapelli_span_cols_eq_of_rank_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/RoucheCapelli.lean)
-/
@[path]
private lemma roucheCapelli_span_cols_eq_of_rank_eq {m n K : Type*} [Fintype n]
  [Field K] (A : Matrix m n K) (b : m → K)
  (hrank :
    A.rank =
      (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
        Matrix m (n ⊕ Fin 1) K).rank) :
  Submodule.span K (Set.range A.col) =
    Submodule.span K
      (Set.range
        (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
          Matrix m (n ⊕ Fin 1) K).col) := by
  let :
    FiniteDimensional K
      (Submodule.span K
        (Set.range
          (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
            Matrix m (n ⊕ Fin 1) K).col)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range _)
  apply Submodule.eq_of_le_of_finrank_eq (roucheCapelli_span_cols_le_augmented A b)
  rw [← Matrix.rank_eq_finrank_span_cols A,
    ← Matrix.rank_eq_finrank_span_cols
      (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
        Matrix m (n ⊕ Fin 1) K)]
  exact hrank

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rouche_capelli](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/RoucheCapelli.lean)
-/
@[path]
lemma rouche_capelli
  [Fintype n] [Field K]
  {A : Matrix m n K}
  {b : m → K} :
-- imply
  (∃ x : n → K, A *ᵥ x = b) ↔
    A.rank =
    (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
    Matrix m (n ⊕ Fin 1) K).rank := by
-- proof
  rw [roucheCapelli_solvable_iff_mem_span_cols A b]
  constructor
  · intro hb
    rw [Matrix.rank_eq_finrank_span_cols A,
      Matrix.rank_eq_finrank_span_cols
        (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
          Matrix m (n ⊕ Fin 1) K),
      roucheCapelli_span_augmented_eq_of_mem A b hb]
  · intro hrank
    rw [roucheCapelli_span_cols_eq_of_rank_eq A b hrank,
      roucheCapelli_range_augmented_cols A b]
    exact Submodule.subset_span (Set.mem_insert b _)

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
