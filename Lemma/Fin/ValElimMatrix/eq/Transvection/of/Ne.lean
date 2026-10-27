import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.IwahoriGLnHelpers
open Matrix DVRContext


/--
[elimMatrix_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
@[path]
private lemma main
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {i j : Fin n}
  {c : C.k}
-- given
  (hij : i ≠ j) :
-- imply
  (elimMatrix C i j hij c).val = transvection i j c :=
-- proof
  rfl



/--
[elim_matrix_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma elim_matrix_mul
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {i j : Fin n}
  {c : C.k}
  {A : Matrix (Fin n) (Fin n) C.k}
  {b : Fin n} :
-- imply
  (transvection i j c * A) i b = A i b + c * A j b := by
-- proof
  simp [transvection, Matrix.add_mul]



/--
[elim_matrix_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma elim_matrix_inv
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {i j : Fin n}
  {c : C.k}
-- given
  (hij : i ≠ j) :
-- imply
  (elimMatrix C i j hij c)⁻¹ = elimMatrix C i j hij (-c) := by
-- proof
  ext1
  simp only [elimMatrix]
  rfl



/--
[elim_matrix_mul_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma elim_matrix_mul_ne
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {i j : Fin n}
  {c : C.k}
  {A : Matrix (Fin n) (Fin n) C.k}
  {a b : Fin n}
-- given
  (ha : a ≠ i) :
-- imply
  (transvection i j c * A) a b = A a b := by
-- proof
  simp [transvection, Matrix.add_mul, ha]



/--
[elim_matrix_upper_unitriangular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma elim_matrix_upper_unitriangular
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {i j : Fin n}
  {c : C.k}
-- given
  (hij : i ≠ j)
  (hlt : i.val < j.val) :
-- imply
  elimMatrix C i j hij c ∈ UpperUnipGLn C n := by
-- proof
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · simp only [elimMatrix_val, transvection, add_apply, one_apply_eq, single_apply,
    show ¬(i = a ∧ j = a) from fun ⟨h1, h2⟩ => hij (h1.trans h2.symm), ite_false, add_zero]
  · have hab' : a ≠ b := by intro h; subst h; omega
    simp only [elimMatrix_val, transvection, add_apply, one_apply_ne hab', single_apply,
      show ¬(i = a ∧ j = b) from fun ⟨h1, h2⟩ => by subst h1; subst h2; omega,
      ite_false, add_zero]



/--
[elim_matrix_lower_unitriangular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma elim_matrix_lower_unitriangular
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {i j : Fin n}
  {c : C.k}
-- given
  (hij : i ≠ j)
  (hgt : i.val > j.val) :
-- imply
  elimMatrix C i j hij c ∈ LowerUnipGLn C n := by
-- proof
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · simp only [elimMatrix_val, transvection, add_apply, one_apply_eq, single_apply,
    show ¬(i = a ∧ j = a) from fun ⟨h1, h2⟩ => hij (h1.trans h2.symm), ite_false, add_zero]
  · have hab' : a ≠ b := by intro h; subst h; omega
    simp only [elimMatrix_val, transvection, add_apply, one_apply_ne hab', single_apply,
      show ¬(i = a ∧ j = b) from fun ⟨h1, h2⟩ => by subst h1; subst h2; omega,
      ite_false, add_zero]



/--
[elim_matrix_iwahori_upper](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma elim_matrix_iwahori_upper
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {i j : Fin n}
  {c : C.k}
-- given
  (hij : i ≠ j)
  (hlt : i.val < j.val)
  (hc : C.isInO c) :
-- imply
  elimMatrix C i j hij c ∈ IwahoriGLn C n := by
-- proof
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b hab => ?_⟩
  ·
    have : (elimMatrix C i j hij c).val a a = 1 := by
      simp only [elimMatrix_val, transvection, add_apply, one_apply_eq, single_apply,
        show ¬(i = a ∧ j = a) from fun ⟨h1, h2⟩ => hij (h1.trans h2.symm), ite_false, add_zero]
    rw [this]; exact C.isUnitInO_one
  ·
    have hab' : a ≠ b := by intro h; subst h; omega
    simp only [elimMatrix_val, transvection, add_apply, one_apply_ne hab', single_apply, zero_add]
    split_ifs with h
    · exact hc
    · exact DVRClosure.isInO_zero
  ·
    have hab' : a ≠ b := by intro h; subst h; omega
    have : (elimMatrix C i j hij c).val a b = 0 := by
      simp only [elimMatrix_val, transvection, add_apply, one_apply_ne hab', single_apply,
        show ¬(i = a ∧ j = b) from fun ⟨h1, h2⟩ => by subst h1; subst h2; omega,
        ite_false, add_zero]
    rw [this]; exact C.isInMaxIdeal_zero



/--
[elim_matrix_iwahori_lower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma elim_matrix_iwahori_lower
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {i j : Fin n}
  {c : C.k}
-- given
  (hij : i ≠ j)
  (hgt : i.val > j.val)
  (hc : C.isInMaxIdeal c) :
-- imply
  elimMatrix C i j hij c ∈ IwahoriGLn C n := by
-- proof
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b hab => ?_⟩
  ·
    have : (elimMatrix C i j hij c).val a a = 1 := by
      simp only [elimMatrix_val, transvection, add_apply, one_apply_eq, single_apply,
        show ¬(i = a ∧ j = a) from fun ⟨h1, h2⟩ => hij (h1.trans h2.symm), ite_false, add_zero]
    rw [this]; exact C.isUnitInO_one
  ·
    have hab' : a ≠ b := by intro h; subst h; omega
    have : (elimMatrix C i j hij c).val a b = 0 := by
      simp only [elimMatrix_val, transvection, add_apply, one_apply_ne hab', single_apply,
        show ¬(i = a ∧ j = b) from fun ⟨h1, h2⟩ => by subst h1; subst h2; omega,
        ite_false, add_zero]
    rw [this]; exact DVRClosure.isInO_zero
  ·
    have hab' : a ≠ b := by intro h; subst h; omega
    simp only [elimMatrix_val, transvection, add_apply, one_apply_ne hab', single_apply, zero_add]
    split_ifs with h
    · exact hc
    · exact C.isInMaxIdeal_zero



/--
[finBlockEquiv_inl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma finBlockEquiv_inl
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {n : ℕ} :
-- imply
  (finBlockEquiv n) (Sum.inl (0 : Fin 1)) = (0 : Fin (n + 1)) := by
-- proof
  simp [finBlockEquiv, finSumFinEquiv, Fin.castOrderIso, Fin.ext_iff]



/--
[finBlockEquiv_inr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma finBlockEquiv_inr
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {n : ℕ}
  {k : Fin n} :
-- imply
  (finBlockEquiv n) (Sum.inr k) = ⟨k.val + 1, by omega⟩ := by
-- proof
  simp [finBlockEquiv, finSumFinEquiv, Fin.castOrderIso, Fin.natAdd, Fin.ext_iff]; omega



/--
[finBlockEquiv_symm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma finBlockEquiv_symm_zero
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {n : ℕ} :
-- imply
  (finBlockEquiv n).symm 0 = Sum.inl 0 := by
-- proof
  have := finBlockEquiv_inl n; rw [← this]; simp [Equiv.symm_apply_apply]



/--
[finBlockEquiv_symm_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma finBlockEquiv_symm_succ
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {n : ℕ}
  {k : Fin n} :
-- imply
  (finBlockEquiv n).symm ⟨k.val + 1, by omega⟩ = Sum.inr k := by
-- proof
  have := finBlockEquiv_inr n k; rw [← this]; simp [Equiv.symm_apply_apply]



/--
[fin_succ_cases](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma fin_succ_cases
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {n : ℕ}
  {p : Fin (n + 1)} :
-- imply
  p = 0 ∨ ∃ k : Fin n, p = ⟨k.val + 1, by omega⟩ := by
-- proof
  obtain h | h := Nat.eq_zero_or_pos p.val
  · left; exact Fin.ext h
  · right; exact ⟨⟨p.val - 1, by omega⟩, by simp [Fin.ext_iff]; omega⟩



/--
[blockEmbedMatrix_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma blockEmbedMatrix_zero_zero
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) C.k} :
-- imply
  blockEmbedMatrix C A 0 0 = 1 := by
-- proof
  simp only [blockEmbedMatrix, reindexAlgEquiv_apply, reindex_apply, submatrix_apply,
    finBlockEquiv_symm_zero, fromBlocks_apply₁₁, one_apply_eq]



/--
[blockEmbedMatrix_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma blockEmbedMatrix_zero_succ
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) C.k}
  {k : Fin n} :
-- imply
  blockEmbedMatrix C A 0 ⟨k.val + 1, by omega⟩ = 0 := by
-- proof
  simp only [blockEmbedMatrix, reindexAlgEquiv_apply, reindex_apply, submatrix_apply,
    finBlockEquiv_symm_zero, finBlockEquiv_symm_succ, fromBlocks_apply₁₂, Matrix.zero_apply]



/--
[blockEmbedMatrix_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma blockEmbedMatrix_succ_zero
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) C.k}
  {k : Fin n} :
-- imply
  blockEmbedMatrix C A ⟨k.val + 1, by omega⟩ 0 = 0 := by
-- proof
  simp only [blockEmbedMatrix, reindexAlgEquiv_apply, reindex_apply, submatrix_apply,
    finBlockEquiv_symm_zero, finBlockEquiv_symm_succ, fromBlocks_apply₂₁, Matrix.zero_apply]



/--
[blockEmbedMatrix_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma blockEmbedMatrix_succ_succ
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) C.k}
  {k l : Fin n} :
-- imply
  blockEmbedMatrix C A ⟨k.val + 1, by omega⟩ ⟨l.val + 1, by omega⟩ = A k l := by
-- proof
  simp only [blockEmbedMatrix, reindexAlgEquiv_apply, reindex_apply, submatrix_apply,
    finBlockEquiv_symm_succ, fromBlocks_apply₂₂]



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
[block_embed_preserves_iwahori](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma block_embed_preserves_iwahori
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {g : GL (Fin n) C.k}
-- given
  (hg : g ∈ IwahoriGLn C n) :
-- imply
  blockEmbedGL C g ∈ IwahoriGLn C (n + 1) := by
-- proof
  obtain ⟨hdiag, habove, hbelow⟩ := hg
  refine ⟨fun p => ?_, fun p q hpq => ?_, fun p q hpq => ?_⟩
  ·
    obtain rfl | ⟨k, rfl⟩ := fin_succ_cases p
    · simp only [blockEmbedGL_val, blockEmbedMatrix_zero_zero C]; exact C.isUnitInO_one
    · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_succ C]; exact hdiag k
  ·
    obtain rfl | ⟨k, rfl⟩ := fin_succ_cases p
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · exact absurd hpq (lt_irrefl _)
      · simp only [blockEmbedGL_val, blockEmbedMatrix_zero_succ C]; exact DVRClosure.isInO_zero
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · exact absurd hpq (Nat.not_lt_zero _)
      · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_succ C]
        exact habove k l (Nat.lt_of_add_lt_add_right hpq)
  ·
    obtain rfl | ⟨k, rfl⟩ := fin_succ_cases p
    · exact absurd hpq (Nat.not_lt_zero _)
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_zero C]; exact C.isInMaxIdeal_zero
      · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_succ C]
        exact hbelow k l (Nat.lt_of_add_lt_add_right hpq)



/--
[block_embed_preserves_upper_unip](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma block_embed_preserves_upper_unip
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {g : GL (Fin n) C.k}
-- given
  (hg : g ∈ UpperUnipGLn C n) :
-- imply
  blockEmbedGL C g ∈ UpperUnipGLn C (n + 1) := by
-- proof
  obtain ⟨hdiag, hbelow⟩ := hg
  refine ⟨fun p => ?_, fun p q hpq => ?_⟩
  ·
    obtain rfl | ⟨k, rfl⟩ := fin_succ_cases p
    · simp only [blockEmbedGL_val, blockEmbedMatrix_zero_zero C]
    · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_succ C]; exact hdiag k
  ·
    obtain rfl | ⟨k, rfl⟩ := fin_succ_cases p
    · exact absurd hpq (Nat.not_lt_zero _)
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_zero C]
      · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_succ C]
        exact hbelow k l (Nat.lt_of_add_lt_add_right hpq)



/--
[block_embed_preserves_lower_unip](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma block_embed_preserves_lower_unip
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {g : GL (Fin n) C.k}
-- given
  (hg : g ∈ LowerUnipGLn C n) :
-- imply
  blockEmbedGL C g ∈ LowerUnipGLn C (n + 1) := by
-- proof
  obtain ⟨hdiag, habove⟩ := hg
  refine ⟨fun p => ?_, fun p q hpq => ?_⟩
  ·
    obtain rfl | ⟨k, rfl⟩ := fin_succ_cases p
    · simp only [blockEmbedGL_val, blockEmbedMatrix_zero_zero C]
    · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_succ C]; exact hdiag k
  ·
    obtain rfl | ⟨k, rfl⟩ := fin_succ_cases p
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · exact absurd hpq (lt_irrefl _)
      · simp only [blockEmbedGL_val, blockEmbedMatrix_zero_succ C]
    · rcases fin_succ_cases q with rfl | ⟨l, rfl⟩
      · exact absurd hpq (Nat.not_lt_zero _)
      · simp only [blockEmbedGL_val, blockEmbedMatrix_succ_succ C]
        exact habove k l (Nat.lt_of_add_lt_add_right hpq)



/--
[isInMaxIdeal_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma isInMaxIdeal_add
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {x y : C.k}
-- given
  (hx : C.isInMaxIdeal x)
  (hy : C.isInMaxIdeal y) :
-- imply
  C.isInMaxIdeal (x + y) := by
-- proof
  obtain ⟨rx, hrx_mem, hrx⟩ := hx; obtain ⟨ry, hry_mem, hry⟩ := hy
  exact ⟨rx + ry, Ideal.add_mem _ hrx_mem hry_mem, by rw [map_add, hrx, hry]⟩



/--
[isInO_mul_isInMaxIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma isInO_mul_isInMaxIdeal
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {x y : C.k}
-- given
  (hx : C.isInO x)
  (hy : C.isInMaxIdeal y) :
-- imply
  C.isInMaxIdeal (x * y) := by
-- proof
  obtain ⟨rx, hrx⟩ := hx; obtain ⟨ry, hry_mem, hry⟩ := hy
  exact ⟨rx * ry, Ideal.mul_mem_left _ rx hry_mem, by rw [map_mul, hrx, hry]⟩



/--
[isUnitInO_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma isUnitInO_mul
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {x y : C.k}
-- given
  (hx : C.isUnitInO x)
  (hy : C.isUnitInO y) :
-- imply
  C.isUnitInO (x * y) := by
-- proof
  obtain ⟨rx, hrx_unit, hrx⟩ := hx; obtain ⟨ry, hry_unit, hry⟩ := hy
  exact ⟨rx * ry, hrx_unit.mul hry_unit, by rw [map_mul, hrx, hry]⟩



/--
[isUnitInO_add_isInMaxIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma isUnitInO_add_isInMaxIdeal
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {x y : C.k}
-- given
  (hx : C.isUnitInO x)
  (hy : C.isInMaxIdeal y) :
-- imply
  C.isUnitInO (x + y) := by
-- proof
  rw [show x + y = x - (-y) from by ring]
  apply DVRClosureGL2.isUnitInO_sub_isInMaxIdeal hx
  obtain ⟨ry, hry_mem, hry⟩ := hy
  exact ⟨-ry, C.maxIdeal.neg_mem hry_mem, by rw [map_neg, hry]⟩



/--
[isInMaxIdeal_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma isInMaxIdeal_finset_sum
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {s : Finset ι}
  {f : ι → C.k}
-- given
  (hf : ∀ i ∈ s, C.isInMaxIdeal (f i)) :
-- imply
  C.isInMaxIdeal (∑ i ∈ s, f i) := by
-- proof
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact C.isInMaxIdeal_zero
  | @insert a s' hna ih =>
    rwa [Finset.sum_insert hna]
      (hf _ (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))



/--
[isInO_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma isInO_finset_sum
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {s : Finset ι}
  {f : ι → C.k}
-- given
  (hf : ∀ i ∈ s, C.isInO (f i)) :
-- imply
  C.isInO (∑ i ∈ s, f i) := by
-- proof
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact DVRClosure.isInO_zero
  | @insert a s' hna ih =>
    rwa [Finset.sum_insert hna]
      (hf _ (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))



/--
[iwahori_entry_isInO'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma iwahori_entry_isInO'
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {g : GL (Fin n) C.k}
  {i j : Fin n}
-- given
  (hg : g ∈ IwahoriGLn C n) :
-- imply
  C.isInO (g.val i j) := by
-- proof
  obtain ⟨hdiag, habove, hbelow⟩ := hg
  obtain h | h | h := lt_trichotomy i.val j.val
  · exact habove i j h
  · have hij : i = j := Fin.ext h
    subst hij; exact C.isUnitInO_isInO (hdiag i)
  · exact C.isInMaxIdeal_isInO (hbelow i j h)



/--
[iwahori_entry_below'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma iwahori_entry_below'
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
  {g : GL (Fin n) C.k}
  {i j : Fin n}
-- given
  (hg : g ∈ IwahoriGLn C n)
  (hij : i.val > j.val) :
-- imply
  C.isInMaxIdeal (g.val i j) :=
-- proof
  hg.2.2 i j hij



/--
[IwahoriGLn_mul_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/IwahoriGLnHelpers.lean)
-/
private lemma IwahoriGLn_mul_mem
  {C : DVRContext}
  [DVRClosureGL2 C]
  {n : ℕ}
-- given
  (g h : GL (Fin n) C.k)
  (hg : g ∈ IwahoriGLn C n)
  (hh : h ∈ IwahoriGLn C n) :
-- imply
  g * h ∈ IwahoriGLn C n := by
-- proof
  have hg_diag := hg.1
  have hg_above := hg.2.1
  have hg_below := hg.2.2
  have hh_diag := hh.1
  have hh_above := hh.2.1
  have hh_below := hh.2.2
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  ·
    show C.isUnitInO ((g * h).val i i)
    have hmul : (g * h).val i i = ∑ k : Fin n, g.val i k * h.val k i := by
      show (g.val * h.val) i i = _; simp [Matrix.mul_apply]
    rw [hmul, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    apply C.isUnitInO_add_isInMaxIdeal
    · exact C.isUnitInO_mul (hg_diag i) (hh_diag i)
    · apply C.isInMaxIdeal_finset_sum
      intro k hk
      rw [Finset.mem_erase] at hk
      obtain hki | hki := lt_or_gt_of_ne (Fin.val_ne_of_ne hk.1)
      ·
        exact DVRClosureGL2.isInMaxIdeal_mul_isInO (hg_below i k hki)
          (C.iwahori_entry_isInO' h hh k i)
      ·
        exact C.isInO_mul_isInMaxIdeal
          (C.iwahori_entry_isInO' g hg i k) (hh_below k i hki)
  ·
    show C.isInO ((g * h).val i j)
    have hmul : (g * h).val i j = ∑ k : Fin n, g.val i k * h.val k j := by
      show (g.val * h.val) i j = _; simp [Matrix.mul_apply]
    rw [hmul]
    apply C.isInO_finset_sum
    intro k _
    exact DVRClosure.isInO_mul (C.iwahori_entry_isInO' g hg i k)
      (C.iwahori_entry_isInO' h hh k j)
  ·
    show C.isInMaxIdeal ((g * h).val i j)
    have hmul : (g * h).val i j = ∑ k : Fin n, g.val i k * h.val k j := by
      show (g.val * h.val) i j = _; simp [Matrix.mul_apply]
    rw [hmul]
    apply C.isInMaxIdeal_finset_sum
    intro k _
    obtain hkj | hkj := le_or_gt k.val j.val
    ·
      exact DVRClosureGL2.isInMaxIdeal_mul_isInO
        (hg_below i k (by omega)) (C.iwahori_entry_isInO' h hh k j)
    ·
      exact C.isInO_mul_isInMaxIdeal
        (C.iwahori_entry_isInO' g hg i k) (hh_below k j hkj)



-- created on 2026-10-23
-- updated on 2026-10-26
