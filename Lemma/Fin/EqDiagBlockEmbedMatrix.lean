import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.DiagBlockEmbed.Part2
open Matrix DVRContext

/--
[finBlockEquiv_inl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma finBlockEquiv_inl
  {n : ℕ} :
-- imply
  (finBlockEquiv n) (Sum.inl (0 : Fin 1)) = (0 : Fin (n + 1)) := by
-- proof
  simp [finBlockEquiv, finSumFinEquiv, Fin.castOrderIso, Fin.ext_iff]



/--
[finBlockEquiv_inr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma finBlockEquiv_inr
  {n : ℕ}
  {k : Fin n} :
-- imply
  (finBlockEquiv n) (Sum.inr k) = k.succ := by
-- proof
  apply Fin.ext
  simp [finBlockEquiv, finSumFinEquiv, Fin.castOrderIso, Fin.natAdd, Fin.succ]
  omega



/--
[finBlockEquiv_symm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma finBlockEquiv_symm_zero
  {n : ℕ} :
-- imply
  (finBlockEquiv n).symm 0 = Sum.inl 0 := by
-- proof
  have := finBlockEquiv_inl (n := n); rw [← this]; simp [Equiv.symm_apply_apply]



/--
[finBlockEquiv_symm_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma finBlockEquiv_symm_succ
  {n : ℕ}
  {k : Fin n} :
-- imply
  (finBlockEquiv n).symm k.succ = Sum.inr k := by
-- proof
  have := finBlockEquiv_inr (n := n) (k := k); rw [← this]; simp [Equiv.symm_apply_apply]



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
  simp only [diagBlockEmbedMatrix, coe_reindexAlgEquiv, reindex_apply, submatrix_apply,
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
  diagBlockEmbedMatrix C a A 0 k.succ = 0 := by
-- proof
  simp only [diagBlockEmbedMatrix, coe_reindexAlgEquiv, reindex_apply, submatrix_apply,
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
  diagBlockEmbedMatrix C a A k.succ 0 = 0 := by
-- proof
  simp only [diagBlockEmbedMatrix, coe_reindexAlgEquiv, reindex_apply, submatrix_apply,
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
  diagBlockEmbedMatrix C a A k.succ l.succ = A k l := by
-- proof
  simp only [diagBlockEmbedMatrix, coe_reindexAlgEquiv, reindex_apply, submatrix_apply,
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
[isInMaxIdeal_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/IwahoriDecomp.lean)
-/
private lemma isInMaxIdeal_zero
  {C : DVRContext}
  [DVRClosureGL2 C] :
-- imply
  C.isInMaxIdeal (0 : C.k) :=
-- proof
  ⟨0, Ideal.zero_mem _, C.embed.map_zero⟩



/--
[blockEmbedGL_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma blockEmbedGL_val
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {g : GL (Fin n) C.k} :
-- imply
  (blockEmbedGL C g).val = blockEmbedMatrix C g.val :=
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
  obtain rfl | ⟨k, rfl⟩ := p.eq_zero_or_eq_succ
  · rcases q.eq_zero_or_eq_succ with rfl | ⟨l, rfl⟩
    · exact absurd rfl hpq
    · change (diagBlockEmbedGL C a M).val 0 l.succ = 0
      rw [diagBlockEmbedGL_val, diagBlockEmbedMatrix_zero_succ]
  · rcases q.eq_zero_or_eq_succ with rfl | ⟨l, rfl⟩
    · change (diagBlockEmbedGL C a M).val k.succ 0 = 0
      rw [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_zero]
    · change (diagBlockEmbedGL C a M).val k.succ l.succ = 0
      rw [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_succ]
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
    obtain rfl | ⟨k, rfl⟩ := p.eq_zero_or_eq_succ
    ·
      change C.isUnitInO ((diagBlockEmbedGL C a M).val 0 0)
      rw [diagBlockEmbedGL_val, main]
      exact ha
    ·
      change C.isUnitInO ((diagBlockEmbedGL C a M).val k.succ k.succ)
      rw [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_succ]
      exact hdiag k
  ·
    obtain rfl | ⟨k, rfl⟩ := p.eq_zero_or_eq_succ
    · rcases q.eq_zero_or_eq_succ with rfl | ⟨l, rfl⟩
      · exact absurd hpq (lt_irrefl _)
      ·
        change C.isInO ((diagBlockEmbedGL C a M).val 0 l.succ)
        rw [diagBlockEmbedGL_val, diagBlockEmbedMatrix_zero_succ]
        exact DVRClosure.isInO_zero
    · rcases q.eq_zero_or_eq_succ with rfl | ⟨l, rfl⟩
      · exact absurd hpq (Nat.not_lt_zero _)
      ·
        change C.isInO ((diagBlockEmbedGL C a M).val k.succ l.succ)
        rw [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_succ]
        exact habove k l (Nat.lt_of_add_lt_add_right hpq)
  ·
    obtain rfl | ⟨k, rfl⟩ := p.eq_zero_or_eq_succ
    · exact absurd hpq (Nat.not_lt_zero _)
    · rcases q.eq_zero_or_eq_succ with rfl | ⟨l, rfl⟩
      ·
        change C.isInMaxIdeal ((diagBlockEmbedGL C a M).val k.succ 0)
        rw [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_zero]
        exact isInMaxIdeal_zero
      ·
        change C.isInMaxIdeal ((diagBlockEmbedGL C a M).val k.succ l.succ)
        rw [diagBlockEmbedGL_val, diagBlockEmbedMatrix_succ_succ]
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
  rw [← map_mul, fromBlocks_multiply, ← map_mul, fromBlocks_multiply]
  simp


/--
[scalarMat1_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiagBlockEmbed.lean)
-/
private lemma scalarMat1_apply_eq
  {C : DVRContext}
  [DVRClosureGL2 C]
  {a : C.k}
  {i j : Fin 1} :
-- imply
  scalarMat1 C a i j = a := by
-- proof
  apply DVRContext.scalarMat1_apply C a i j


-- created on 2026-10-23
-- updated on 2026-11-13
