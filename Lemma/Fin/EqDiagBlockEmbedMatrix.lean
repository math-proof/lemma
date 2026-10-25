import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.Building.DiagBlockEmbed.Part2
open Matrix DVRContext


/--
[diagBlockEmbedMatrix_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiagBlockEmbed.lean)
-/
@[path]
private lemma main
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {a : C.k}
  {A : Matrix (Fin n) (Fin n) C.k} :
-- imply
  diagBlockEmbedMatrix C a A 0 0 = a := by
-- proof
  simp only [diagBlockEmbedMatrix, reindexAlgEquiv_apply, reindex_apply, submatrix_apply,
    finBlockEquiv_symm_zero, fromBlocks_apply₁₁, scalarMat1_apply]



/--
[diagBlockEmbedMatrix_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiagBlockEmbed.lean)
-/
private lemma diagBlockEmbedMatrix_zero_succ
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {a : C.k}
  {A : Matrix (Fin n) (Fin n) C.k}
  {k : Fin n} :
-- imply
  diagBlockEmbedMatrix C a A 0 ⟨k.val + 1, by omega⟩ = 0 := by
-- proof
  simp only [diagBlockEmbedMatrix, reindexAlgEquiv_apply, reindex_apply, submatrix_apply,
    finBlockEquiv_symm_zero, finBlockEquiv_symm_succ, fromBlocks_apply₁₂, Matrix.zero_apply]



/--
[diagBlockEmbedMatrix_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiagBlockEmbed.lean)
-/
private lemma diagBlockEmbedMatrix_succ_zero
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {a : C.k}
  {A : Matrix (Fin n) (Fin n) C.k}
  {k : Fin n} :
-- imply
  diagBlockEmbedMatrix C a A ⟨k.val + 1, by omega⟩ 0 = 0 := by
-- proof
  simp only [diagBlockEmbedMatrix, reindexAlgEquiv_apply, reindex_apply, submatrix_apply,
    finBlockEquiv_symm_zero, finBlockEquiv_symm_succ, fromBlocks_apply₂₁, Matrix.zero_apply]



/--
[diagBlockEmbedMatrix_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiagBlockEmbed.lean)
-/
private lemma diagBlockEmbedMatrix_succ_succ
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {a : C.k}
  {A : Matrix (Fin n) (Fin n) C.k}
  {k l : Fin n} :
-- imply
  diagBlockEmbedMatrix C a A ⟨k.val + 1, by omega⟩ ⟨l.val + 1, by omega⟩ = A k l := by
-- proof
  simp only [diagBlockEmbedMatrix, reindexAlgEquiv_apply, reindex_apply, submatrix_apply,
    finBlockEquiv_symm_succ, fromBlocks_apply₂₂]



/--
[diagBlockEmbedGL_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiagBlockEmbed.lean)
-/
private lemma diagBlockEmbedGL_val
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {a : C.kˣ}
  {M : GL (Fin n) C.k} :
-- imply
  (diagBlockEmbedGL C a M).val = diagBlockEmbedMatrix C a.val M.val :=
-- proof
  rfl



/--
[diagBlockEmbed_preserves_diag](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiagBlockEmbed.lean)
-/
private lemma diagBlockEmbed_preserves_diag
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {a : C.kˣ}
  {M : GL (Fin n) C.k}
-- given
  (hM : M ∈ DiagGLn C n) :
-- imply
  diagBlockEmbedGL C a M ∈ DiagGLn C (n + 1) := by
-- proof
  intro p q hpq
  obtain rfl | ⟨k, rfl⟩ := fin_succ_cases p
  · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
    · exact absurd rfl hpq
    · simp
  · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
    · simp
    · simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_succ]
      exact hM k l (by intro h; apply hpq; subst h; rfl)



/--
[diagBlockEmbed_preserves_iwahori](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiagBlockEmbed.lean)
-/
private lemma diagBlockEmbed_preserves_iwahori
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {a : C.kˣ}
  {M : GL (Fin n) C.k}
-- given
  (ha : C.isUnitInO a.val)
  (hM : M ∈ IwahoriGLn C n) :
-- imply
  diagBlockEmbedGL C a M ∈ IwahoriGLn C (n + 1) := by
-- proof
  obtain ⟨hdiag, habove, hbelow⟩ := hM
  refine ⟨fun p => ?_, fun p q hpq => ?_, fun p q hpq => ?_⟩
  ·
    obtain rfl | ⟨k, rfl⟩ := fin_succ_cases p
    · simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_zero_zero]; exact ha
    · simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_succ]; exact hdiag k
  ·
    obtain rfl | ⟨k, rfl⟩ := fin_succ_cases p
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · exact absurd hpq (lt_irrefl _)
      · simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_zero_succ]; exact DVRClosure.isInO_zero
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · exact absurd hpq (Nat.not_lt_zero _)
      · simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_succ]
        exact habove k l (Nat.lt_of_add_lt_add_right hpq)
  ·
    obtain rfl | ⟨k, rfl⟩ := fin_succ_cases p
    · exact absurd hpq (Nat.not_lt_zero _)
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_zero]; exact C.isInMaxIdeal_zero
      · simp only [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_succ]
        exact hbelow k l (Nat.lt_of_add_lt_add_right hpq)



/--
[blockEmbed_diagBlockEmbed_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiagBlockEmbed.lean)
-/
private lemma blockEmbed_diagBlockEmbed_mul
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {a : C.kˣ}
  {A M B : GL (Fin n) C.k} :
-- imply
  blockEmbedGL C A * diagBlockEmbedGL C a M * blockEmbedGL C B = diagBlockEmbedGL C a (A * M * B) := by
-- proof
  ext1
  simp only [Units.val_mul, diagBlockEmbedGL_val, blockEmbedGL_val,
    blockEmbedMatrix, diagBlockEmbedMatrix]
  rw [← reindexAlgEquiv_mul, fromBlocks_multiply, ← reindexAlgEquiv_mul, fromBlocks_multiply]
  simp


/--
[scalarMat1_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiagBlockEmbed.lean)
-/
private lemma scalarMat1_apply_eq
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {a : C.k}
  {i j : Fin 1} :
-- imply
  scalarMat1 C a i j = a := by
-- proof
  apply DVRContext.scalarMat1_apply C a i j


-- created on 2026-10-23
-- updated on 2026-10-24
