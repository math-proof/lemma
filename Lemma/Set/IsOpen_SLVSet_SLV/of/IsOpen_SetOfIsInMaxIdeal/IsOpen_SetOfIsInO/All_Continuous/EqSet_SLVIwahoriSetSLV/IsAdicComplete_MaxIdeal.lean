import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.AffineSLVStrong
open AffineBuildingSLVStrong
open AffineBuildingSLV AffineBuildingSLVAxioms


namespace AffineBuildingSLVStrong

/--
[iwahori_is_open_in_SLV](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma iwahori_is_open_in_SLV
  {C : DVRContext}
  [TopologicalSpace C.k]
  [LocallyCompactSpace C.k]
  [IsDiscreteValuationRing C.𝔬]
  {B : Subgroup (SLV C)}
  {τ : TopologicalSpace (SLV C)}
  [htg : @IsTopologicalGroup (SLV C) τ _]
-- given
  (ho_complete : IsAdicComplete (DVRContext.maxIdeal C) C.𝔬)
  (hB_iwahori : (B : Set (SLV C)) = IwahoriSetSLV C)
  (h_entry_cont : ∀ i j : Fin C.n, @Continuous (SLV C) C.k τ _ (matEntryProj C i j))
  (h_valring_open : IsOpen {x : C.k | C.isInO x})
  (h_maxideal_open : IsOpen {x : C.k | C.isInMaxIdeal x}) :
-- imply
  @IsOpen (SLV C) τ (B : Set (SLV C)) := by
-- proof
  rw [hB_iwahori, IwahoriSetSLV]
  apply @isOpen_iInter_of_finite (SLV C) (Fin C.n) τ
  intro i
  apply @isOpen_iInter_of_finite (SLV C) (Fin C.n) τ
  intro j
  apply (h_entry_cont i j).isOpen_preimage
  unfold iwahoriEntryCondition
  split
  · exact h_maxideal_open
  · exact h_valring_open

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[iwahori_is_closed_in_SLV](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma iwahori_is_closed_in_SLV
  {C : DVRContext}
  [TopologicalSpace C.k]
  [LocallyCompactSpace C.k]
  [IsDiscreteValuationRing C.𝔬]
  {B : Subgroup (SLV C)}
  {τ : TopologicalSpace (SLV C)}
  [htg : @IsTopologicalGroup (SLV C) τ _]
-- given
  (ho_complete : IsAdicComplete (DVRContext.maxIdeal C) C.𝔬)
  (hB_open : @IsOpen (SLV C) τ (B : Set (SLV C))) :
-- imply
  @IsClosed (SLV C) τ (B : Set (SLV C)) := by
-- proof
  have : @SeparatelyContinuousMul (SLV C) τ _ := by
    haveI : @ContinuousMul (SLV C) τ _ := htg.toContinuousMul
    infer_instance
  exact @Subgroup.isClosed_of_isOpen (SLV C) _ τ this B hB_open

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[iwahori_is_compact_in_SLV](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma iwahori_is_compact_in_SLV
  {C : DVRContext}
  [TopologicalSpace C.k]
  [LocallyCompactSpace C.k]
  [IsDiscreteValuationRing C.𝔬]
  {B : Subgroup (SLV C)}
  {τ : TopologicalSpace (SLV C)}
  [htg : @IsTopologicalGroup (SLV C) τ _]
-- given
  (ho_complete : IsAdicComplete (DVRContext.maxIdeal C) C.𝔬)
  (hB_closed : @IsClosed (SLV C) τ (B : Set (SLV C)))
  (hB_in_compact : ∃ (K : Set (SLV C)), @IsCompact (SLV C) τ K ∧ (B : Set (SLV C)) ⊆ K) :
-- imply
  @IsCompact (SLV C) τ (B : Set (SLV C)) := by
-- proof
  obtain ⟨K, hK_compact, hBK⟩ := hB_in_compact
  exact closed_in_compact_is_compact (↑B) K hB_closed hBK hK_compact

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[mem_imageSubring_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma mem_imageSubring_iff
  {C : DVRContext}
  {x : C.k} :
-- imply
  x ∈ imageSubring C ↔ C.isInO x := by
-- proof
  simp [imageSubring, RingHom.mem_range, DVRContext.isInO]

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[isInMaxIdeal_add'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma isInMaxIdeal_add'
  {C : DVRContext}
  {x y : C.k}
-- given
  (hx : C.isInMaxIdeal x)
  (hy : C.isInMaxIdeal y) :
-- imply
  C.isInMaxIdeal (x + y) := by
-- proof
  obtain ⟨rx, hrx_mem, hrx⟩ := hx; obtain ⟨ry, hry_mem, hry⟩ := hy
  exact ⟨rx + ry, Ideal.add_mem _ hrx_mem hry_mem, by rw [map_add, hrx, hry]⟩

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[isInO_mul_isInMaxIdeal'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma isInO_mul_isInMaxIdeal'
  {C : DVRContext}
  {x y : C.k}
-- given
  (hx : C.isInO x)
  (hy : C.isInMaxIdeal y) :
-- imply
  C.isInMaxIdeal (x * y) := by
-- proof
  obtain ⟨rx, hrx⟩ := hx; obtain ⟨ry, hry_mem, hry⟩ := hy
  exact ⟨rx * ry, Ideal.mul_mem_left _ rx hry_mem, by rw [map_mul, hrx, hry]⟩

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[isInMaxIdeal_mul_isInO'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma isInMaxIdeal_mul_isInO'
  {C : DVRContext}
  {x y : C.k}
-- given
  (hx : C.isInMaxIdeal x)
  (hy : C.isInO y) :
-- imply
  C.isInMaxIdeal (x * y) := by
-- proof
  obtain ⟨rx, hrx_mem, hrx⟩ := hx; obtain ⟨ry, hry⟩ := hy
  exact ⟨rx * ry, Ideal.mul_mem_right ry _ hrx_mem, by rw [map_mul, hrx, hry]⟩

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[isInMaxIdeal_zero'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma isInMaxIdeal_zero'
  {C : DVRContext} :
-- imply
  C.isInMaxIdeal 0 :=
-- proof
  ⟨0, Ideal.zero_mem _, map_zero _⟩

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[isInO_one'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma isInO_one'
  {C : DVRContext} :
-- imply
  C.isInO 1 :=
-- proof
  ⟨1, map_one _⟩

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[isInO_zero'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma isInO_zero'
  {C : DVRContext} :
-- imply
  C.isInO 0 :=
-- proof
  ⟨0, map_zero _⟩

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[isInO_neg'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma isInO_neg'
  {C : DVRContext}
  {x : C.k}
-- given
  (hx : C.isInO x) :
-- imply
  C.isInO (-x) := by
-- proof
  obtain ⟨rx, hrx⟩ := hx; exact ⟨-rx, by rw [map_neg, hrx]⟩

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[isInO_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma isInO_finset_sum
  {C : DVRContext}
  {s : Finset ι}
  {f : ι → C.k}
-- given
  (hf : ∀ x ∈ s, C.isInO (f x)) :
-- imply
  C.isInO (∑ x ∈ s, f x) := by
-- proof
  rw [← mem_imageSubring_iff]
  exact Subring.sum_mem _ (fun x hx => (mem_imageSubring_iff C _).mpr (hf x hx))

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[isInMaxIdeal_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma isInMaxIdeal_finset_sum
  {C : DVRContext}
  {s : Finset ι}
  {f : ι → C.k}
-- given
  (hf : ∀ x ∈ s, C.isInMaxIdeal (f x)) :
-- imply
  C.isInMaxIdeal (∑ x ∈ s, f x) := by
-- proof
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact isInMaxIdeal_zero' C
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isInMaxIdeal_add' C (hf _ (Finset.mem_insert_self _ _))
      (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[isInO_finset_prod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma isInO_finset_prod
  {C : DVRContext}
  {s : Finset ι}
  {f : ι → C.k}
-- given
  (hf : ∀ x ∈ s, C.isInO (f x)) :
-- imply
  C.isInO (∏ x ∈ s, f x) := by
-- proof
  rw [← mem_imageSubring_iff]
  exact Subring.prod_mem _ (fun x hx => (mem_imageSubring_iff C _).mpr (hf x hx))

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[mem_IwahoriSetSLV_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma mem_IwahoriSetSLV_iff
  {C : DVRContext}
  {g : SLV C} :
-- imply
  g ∈ IwahoriSetSLV C ↔ ∀ i j : Fin C.n, (g : Matrix (Fin C.n) (Fin C.n) C.k) i j ∈ iwahoriEntryCondition C i j := by
-- proof
  simp only [IwahoriSetSLV, Set.mem_iInter, Set.mem_preimage, matEntryProj]

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[iwahori_entry_isInO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma iwahori_entry_isInO
  {C : DVRContext}
  [IsDiscreteValuationRing C.𝔬]
  {g : SLV C}
  {i j : Fin C.n}
-- given
  (hg : g ∈ IwahoriSetSLV C) :
-- imply
  C.isInO ((g : Matrix (Fin C.n) (Fin C.n) C.k) i j) := by
-- proof
  have hg' := (mem_IwahoriSetSLV_iff C g).mp hg i j
  simp only [iwahoriEntryCondition] at hg'
  split_ifs at hg' with h
  · exact C.isInMaxIdeal_isInO hg'
  · exact hg'

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[iwahori_entry_below](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma iwahori_entry_below
  {C : DVRContext}
  [IsDiscreteValuationRing C.𝔬]
  {g : SLV C}
  {i j : Fin C.n}
-- given
  (hg : g ∈ IwahoriSetSLV C)
  (hij : i.val > j.val) :
-- imply
  C.isInMaxIdeal ((g : Matrix (Fin C.n) (Fin C.n) C.k) i j) := by
-- proof
  have hg' := (mem_IwahoriSetSLV_iff C g).mp hg i j
  simp only [iwahoriEntryCondition, hij, if_true, Set.mem_setOf_eq] at hg'
  exact hg'

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[sign_isInO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma sign_isInO
  {C : DVRContext}
  {σ : Equiv.Perm (Fin C.n)} :
-- imply
  C.isInO ((Equiv.Perm.sign σ : ℤ) : C.k) := by
-- proof
  have : (Equiv.Perm.sign σ : ℤ) = 1 ∨ (Equiv.Perm.sign σ : ℤ) = -1 := by
    obtain h | h <;> simp [h] := Int.units_eq_one_or (Equiv.Perm.sign σ)
  obtain h | h := this
  · rw [h, Int.cast_one]; exact isInO_one' C
  · rw [h, Int.cast_neg, Int.cast_one]; exact isInO_neg' C (isInO_one' C)

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[isInO_smul_of_isInO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma isInO_smul_of_isInO
  {C : DVRContext}
  {z : ℤ}
  {x : C.k}
-- given
  (hz : C.isInO (z : C.k))
  (hx : C.isInO x) :
-- imply
  C.isInO (z • x) := by
-- proof
  rw [zsmul_eq_mul]
  rw [← mem_imageSubring_iff] at hz hx ⊢
  exact Subring.mul_mem _ hz hx

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[isInO_det](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma isInO_det
  {C : DVRContext}
  {M : Matrix (Fin C.n) (Fin C.n) C.k}
-- given
  (hM : ∀ i j, C.isInO (M i j)) :
-- imply
  C.isInO M.det := by
-- proof
  simp only [Matrix.det_apply]
  apply isInO_finset_sum
  intro σ _
  exact isInO_smul_of_isInO C _ (sign_isInO C σ)
    (isInO_finset_prod C (fun i _ => hM (σ i) i))

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[perm_has_ascent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma perm_has_ascent
  {n : ℕ}
  {σ : Equiv.Perm (Fin n)}
  {i : Fin n}
-- given
  (hi : (σ i).val < i.val) :
-- imply
  ∃ l : Fin n, l ≠ i ∧ (σ l).val > l.val := by
-- proof
  by_contra h
  push Not at h
  have h_sum : ∑ l : Fin n, ((σ l).val : ℤ) = ∑ l : Fin n, (l.val : ℤ) :=
    Equiv.sum_comp σ (fun l => (l.val : ℤ))
  have h_zero : ∑ l : Fin n, (((σ l).val : ℤ) - l.val) = 0 := by
    simp only [Finset.sum_sub_distrib]; omega
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h_zero
  have hi_neg : ((σ i).val : ℤ) - i.val < 0 := by omega
  have h_rest_nonpos : ∀ l ∈ Finset.univ.erase i, (((σ l).val : ℤ) - l.val) ≤ 0 := by
    intro l hl
    have hli : l ≠ i := Finset.ne_of_mem_erase hl
    exact sub_nonpos.mpr (Int.ofNat_le.mpr (h l hli))
  have h_rest_nonpos' : ∑ l ∈ Finset.univ.erase i, (((σ l).val : ℤ) - l.val) ≤ 0 :=
    Finset.sum_nonpos h_rest_nonpos
  linarith

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[updateRow_isInO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma updateRow_isInO
  {C : DVRContext}
  [IsDiscreteValuationRing C.𝔬]
  {g : SLV C}
  {i j : Fin C.n}
  {l m : Fin C.n}
-- given
  (hg : g ∈ IwahoriSetSLV C) :
-- imply
  C.isInO (((g : Matrix (Fin C.n) (Fin C.n) C.k).updateRow j (Pi.single i 1)) l m) := by
-- proof
  simp only [Matrix.updateRow_apply]
  split_ifs with hlj
  · simp only [Pi.single_apply]
    split_ifs with hmi
    · exact isInO_one' C
    · exact isInO_zero' C
  · exact iwahori_entry_isInO C hg l m

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[adjugate_isInO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma adjugate_isInO
  {C : DVRContext}
  [IsDiscreteValuationRing C.𝔬]
  {g : SLV C}
  {i j : Fin C.n}
-- given
  (hg : g ∈ IwahoriSetSLV C) :
-- imply
  C.isInO ((g : Matrix (Fin C.n) (Fin C.n) C.k).adjugate i j) := by
-- proof
  rw [Matrix.adjugate_apply]
  exact isInO_det C (updateRow_isInO C hg i j)

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[adjugate_below_isInMaxIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma adjugate_below_isInMaxIdeal
  {C : DVRContext}
  [IsDiscreteValuationRing C.𝔬]
  {g : SLV C}
  {i j : Fin C.n}
-- given
  (hg : g ∈ IwahoriSetSLV C)
  (hij : i.val > j.val) :
-- imply
  C.isInMaxIdeal ((g : Matrix (Fin C.n) (Fin C.n) C.k).adjugate i j) := by
-- proof
  rw [Matrix.adjugate_apply]
  set B := (g : Matrix (Fin C.n) (Fin C.n) C.k).updateRow j (Pi.single i 1)
  simp only [Matrix.det_apply]
  apply isInMaxIdeal_finset_sum
  intro σ _
  by_cases hσi : σ i = j
  ·
    have hdesc : (σ i).val < i.val := by rw [hσi]; exact hij
    obtain ⟨l, hli, hlt⟩ := perm_has_ascent hdesc
    have hσlj : σ l ≠ j := by
      intro heq
      have : l = i := σ.injective (heq.trans hσi.symm)
      exact hli this
    have hBl : B (σ l) l = (g : Matrix _ _ C.k) (σ l) l := by
      simp [B, Matrix.updateRow_apply, hσlj]
    have hm : C.isInMaxIdeal ((g : Matrix _ _ C.k) (σ l) l) :=
      iwahori_entry_below C hg hlt
    have hprod : C.isInMaxIdeal (∏ idx : Fin C.n, B (σ idx) idx) := by
      classical
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l), hBl]
      exact isInMaxIdeal_mul_isInO' C hm
        (isInO_finset_prod C (fun m hm' =>
          updateRow_isInO C hg i j (σ m) m))
    rw [Units.smul_def, zsmul_eq_mul]
    exact isInO_mul_isInMaxIdeal' C (sign_isInO C σ) hprod
  ·
    have hzero : ∏ idx : Fin C.n, B (σ idx) idx = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (σ.symm j))
      have h_ne : σ.symm j ≠ i := by
        intro h; exact hσi (by rw [← h, Equiv.apply_symm_apply])
      simp only [B, Matrix.updateRow_apply, Equiv.apply_symm_apply, ↓reduceIte,
        Pi.single_apply, h_ne]
    rw [hzero, smul_zero]
    exact isInMaxIdeal_zero' C

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[iwahori_set_is_subgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma iwahori_set_is_subgroup
  {C : DVRContext}
  [IsDiscreteValuationRing C.𝔬] :
-- imply
  ∃ B : Subgroup (SLV C), (B : Set (SLV C)) = IwahoriSetSLV C := by
-- proof
  refine ⟨{ carrier := IwahoriSetSLV C, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩
  ·
    intro g h hg hh
    rw [mem_IwahoriSetSLV_iff]
    intro i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, iwahoriEntryCondition]
    split_ifs with hij
    ·
      apply isInMaxIdeal_finset_sum
      intro k _
      by_cases hki : i.val > k.val
      · exact isInMaxIdeal_mul_isInO' C (iwahori_entry_below C hg hki)
        (iwahori_entry_isInO C hh k j)
      · exact isInO_mul_isInMaxIdeal' C (iwahori_entry_isInO C hg i k)
        (iwahori_entry_below C hh (by omega))
    ·
      apply isInO_finset_sum
      intro k _
      rw [← mem_imageSubring_iff]
      exact Subring.mul_mem _
        ((mem_imageSubring_iff C _).mpr (iwahori_entry_isInO C hg i k))
        ((mem_imageSubring_iff C _).mpr (iwahori_entry_isInO C hh k j))
  ·
    rw [mem_IwahoriSetSLV_iff]
    intro i j
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply, iwahoriEntryCondition]
    split_ifs with hij heq
    · subst heq; omega
    · exact isInMaxIdeal_zero' C
    · exact isInO_one' C
    · exact isInO_zero' C
  ·
    intro g hg
    rw [mem_IwahoriSetSLV_iff]
    intro i j
    simp only [iwahoriEntryCondition]
    have hinv_entry : (g⁻¹ : SLV C) i j = (g : Matrix _ _ C.k).adjugate i j := by
      show (↑(g⁻¹ : SLV C) : Matrix _ _ C.k) i j = _
      simp [Matrix.SpecialLinearGroup.coe_inv]
    split_ifs with hij
    · rw [Set.mem_setOf_eq, hinv_entry]
      exact adjugate_below_isInMaxIdeal C hg hij
    · rw [Set.mem_setOf_eq, hinv_entry]
      exact adjugate_isInO C hg i j

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[valuation_ring_is_open](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma valuation_ring_is_open
  {C : DVRContext}
  [TopologicalSpace C.k]
  [LocallyCompactSpace C.k]
  [IsDiscreteValuationRing C.𝔬]
  [DVRTopologicalAssumptions C] :
-- imply
  IsOpen {x : C.k | C.isInO x} :=
-- proof
  DVRTopologicalAssumptions.isOpen_valRing

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[maximal_ideal_is_open](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma maximal_ideal_is_open
  {C : DVRContext}
  [TopologicalSpace C.k]
  [LocallyCompactSpace C.k]
  [IsDiscreteValuationRing C.𝔬]
  [DVRTopologicalAssumptions C] :
-- imply
  IsOpen {x : C.k | C.isInMaxIdeal x} :=
-- proof
  DVRTopologicalAssumptions.isOpen_maxIdeal

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[iwahori_in_compact_set](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma iwahori_in_compact_set
  {C : DVRContext}
  [TopologicalSpace C.k]
  [LocallyCompactSpace C.k]
  [IsDiscreteValuationRing C.𝔬]
  [DVRTopologicalAssumptions C]
  {B : Subgroup (SLV C)}
-- given
  (ho_complete : IsAdicComplete (DVRContext.maxIdeal C) C.𝔬)
  (hB_iwahori : (B : Set (SLV C)) = IwahoriSetSLV C) :
-- imply
  ∃ (K : Set (SLV C)), IsCompact K ∧ (B : Set (SLV C)) ⊆ K := by
-- proof
  haveI : IsTopologicalRing C.k := DVRTopologicalAssumptions.isTopologicalRing
  haveI : T1Space C.k := DVRTopologicalAssumptions.t1Space
  refine ⟨{g : SLV C | ∀ i j, (g : Matrix (Fin C.n) (Fin C.n) C.k) i j ∈ {x | C.isInO x}},
    ?_, ?_⟩
  ·
    have hce : Topology.IsClosedEmbedding
      (Subtype.val : SLV C → Matrix (Fin C.n) (Fin C.n) C.k) := by
      refine ⟨Topology.IsEmbedding.subtypeVal, ?_⟩
      rw [Subtype.range_coe_subtype]
      exact isClosed_eq (by fun_prop) continuous_const
    exact hce.isCompact_preimage
      (isCompact_pi_infinite (fun _ => isCompact_pi_infinite
        (fun _ => DVRTopologicalAssumptions.isCompact_valRing)))
  ·
    intro g hg
    simp only [Set.mem_setOf_eq]
    intro i j
    rw [hB_iwahori] at hg
    have h := Set.mem_iInter.mp (Set.mem_iInter.mp hg i) j
    simp only [IwahoriSetSLV, matEntryProj, Set.mem_preimage, iwahoriEntryCondition] at h
    split_ifs at h with hij
    · exact C.isInMaxIdeal_isInO h
    · exact h

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[iwahori_is_compact_open](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma iwahori_is_compact_open
  {C : DVRContext}
  [TopologicalSpace C.k]
  [LocallyCompactSpace C.k]
  [IsDiscreteValuationRing C.𝔬]
  [DVRTopologicalAssumptions C]
-- given
  (ho_complete : IsAdicComplete (DVRContext.maxIdeal C) C.𝔬) :
-- imply
  ∃ (B : Subgroup (SLV C)) (τ : TopologicalSpace (SLV C)) (_ : @IsTopologicalGroup (SLV C) τ _), @IsCompact (SLV C) τ (B : Set (SLV C)) ∧ @IsOpen (SLV C) τ (B : Set (SLV C)) := by
-- proof
  haveI : IsTopologicalRing C.k := DVRTopologicalAssumptions.isTopologicalRing
  haveI : T1Space C.k := DVRTopologicalAssumptions.t1Space
  let τ : TopologicalSpace (SLV C) := inferInstance
  obtain ⟨B, hB_iwahori⟩ := iwahori_set_is_subgroup C
  have h_entry_cont : ∀ i j : Fin C.n,
    @Continuous (SLV C) C.k τ _ (matEntryProj C i j) := by
    intro i j
    show Continuous (fun g : SLV C => (g : Matrix (Fin C.n) (Fin C.n) C.k) i j)
    exact (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  have hB_open : @IsOpen (SLV C) τ (B : Set (SLV C)) := by
    exact @iwahori_is_open_in_SLV C _ _ _ ho_complete B τ inferInstance
      hB_iwahori h_entry_cont (valuation_ring_is_open C) (maximal_ideal_is_open C)
  have hB_closed : @IsClosed (SLV C) τ (B : Set (SLV C)) := by
    exact @iwahori_is_closed_in_SLV C _ _ _ ho_complete B τ inferInstance hB_open
  have hB_compact : @IsCompact (SLV C) τ (B : Set (SLV C)) := by
    exact @iwahori_is_compact_in_SLV C _ _ _ ho_complete B τ inferInstance hB_closed
      (iwahori_in_compact_set C ho_complete B hB_iwahori)
  exact ⟨B, τ, inferInstance, hB_compact, hB_open⟩

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[frame_chamber_transitivity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma frame_chamber_transitivity
  {C : DVRContext}
  [TopologicalSpace C.k]
  [LocallyCompactSpace C.k]
  [IsDiscreteValuationRing C.𝔬]
  {α : SLVAction C}
  {F : Frame C}
  {C₁ C₂ : Simplex C}
-- given
  (ho_complete : IsAdicComplete (DVRContext.maxIdeal C) C.𝔬)
  (hC₁_max : C₁.IsMaximal C)
  (hC₂_max : C₂.IsMaximal C)
  (hC₁ : C₁ ∈ Apartment C F)
  (hC₂ : C₂ ∈ Apartment C F) :
-- imply
  ∃ g : SLV C, α.act_simplex g C₁ = C₂ ∧ α.act_apartment g (Apartment C F) = Apartment C F :=
-- proof
α.act_frame_chamber_trans F C₁ C₂ hC₁_max hC₂_max hC₁ hC₂

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[act_apartment_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma act_apartment_one
  {C : DVRContext}
  {α : SLVAction C}
  {A : Set (Simplex C)} :
-- imply
  α.act_apartment 1 A = A := by
-- proof
  rw [α.act_apartment_eq]
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; rw [α.act_one]; exact hy
  · intro hx; exact ⟨x, hx, α.act_one x⟩

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[act_apartment_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma act_apartment_mul
  {C : DVRContext}
  {α : SLVAction C}
  {g₁ g₂ : SLV C}
  {A : Set (Simplex C)} :
-- imply
  α.act_apartment (g₁ * g₂) A = α.act_apartment g₁ (α.act_apartment g₂ A) := by
-- proof
  simp only [α.act_apartment_eq, Set.image_image]
  congr 1
  ext x
  exact α.act_mul g₁ g₂ x

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[strong_transitivity_from_apt_and_chamber_transit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma strong_transitivity_from_apt_and_chamber_transit
  {C : DVRContext}
  [TopologicalSpace C.k]
  [hDVR : IsDiscreteValuationRing C.𝔬]
  [hk_lc : LocallyCompactSpace C.k]
  {α : SLVAction C}
  {max_apts : Set (Set (Simplex C))}
-- given
  (ho_complete : IsAdicComplete (DVRContext.maxIdeal C) C.𝔬)
  (hframes : ∀ F : Frame C, Apartment C F ∈ max_apts)
  (apt_transit : ∀ (A₁ A₂ : Set (Simplex C)), A₁ ∈ max_apts → A₂ ∈ max_apts → ∃ g : SLV C, α.act_apartment g A₁ = A₂)
  (chamber_transit : ∀ (C₁ C₂ : Simplex C) (A : Set (Simplex C)), C₁.IsMaximal C → C₂.IsMaximal C → A ∈ max_apts → C₁ ∈ A → C₂ ∈ A → ∃ g : SLV C, α.act_simplex g C₁ = C₂ ∧ α.act_apartment g A = A) :
-- imply
  IsStronglyTransitive C α max_apts := by
-- proof
  intro C₁ A₁ C₂ A₂ hC₁_max hC₂_max hA₁ hA₂ hC₁_in_A₁ hC₂_in_A₂
  obtain ⟨g₁, hg₁⟩ := apt_transit A₁ A₂ hA₁ hA₂
  have hg₁C₁_in_A₂ : α.act_simplex g₁ C₁ ∈ A₂ := by
    rw [← hg₁, α.act_apartment_eq]
    exact Set.mem_image_of_mem _ hC₁_in_A₁
  have hg₁C₁_max : (α.act_simplex g₁ C₁).IsMaximal C :=
    α.act_preserves_maximal g₁ C₁ hC₁_max
  obtain ⟨h, hh_chamber, hh_apt⟩ := chamber_transit (α.act_simplex g₁ C₁) C₂ A₂
    hg₁C₁_max hC₂_max hA₂ hg₁C₁_in_A₂ hC₂_in_A₂
  refine ⟨h * g₁, ?_, ?_⟩
  ·
    rwa [α.act_mul]
  ·
    rw [α.act_apartment_eq]
    ext σ
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [α.act_mul]
      have hg₁x_in_A₂ : α.act_simplex g₁ x ∈ A₂ := by
        rw [← hg₁, α.act_apartment_eq]
        exact Set.mem_image_of_mem _ hx
      have h_A₂_surj : (α.act_simplex h) '' A₂ = A₂ := by
        rw [← α.act_apartment_eq]; exact hh_apt
      rw [← h_A₂_surj]
      exact Set.mem_image_of_mem _ hg₁x_in_A₂
    · intro hσ
      have h_A₂_surj : (α.act_simplex h) '' A₂ = A₂ := by
        rw [← α.act_apartment_eq]; exact hh_apt
      rw [← h_A₂_surj] at hσ
      obtain ⟨y, hy_in_A₂, rfl⟩ := hσ
      have g₁_A₁_surj : (α.act_simplex g₁) '' A₁ = A₂ := by
        rw [← α.act_apartment_eq]; exact hg₁
      rw [← g₁_A₁_surj] at hy_in_A₂
      obtain ⟨x, hx_in_A₁, rfl⟩ := hy_in_A₂
      exact ⟨x, hx_in_A₁, α.act_mul h g₁ x⟩

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[constructed_apartment_system_is_maximal_of_stable_and_transitive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma constructed_apartment_system_is_maximal_of_stable_and_transitive
  [Group G]
  [TopologicalSpace G]
  {act : G → Set (Simplex C) → Set (Simplex C)}
  {𝒜 : Set (Set (Simplex C))}
  {max_apts : Set (Set (Simplex C))}
  {A₀ : Set (Simplex C)}
-- given
  (hact_mul : ∀ g₁ g₂ : G, ∀ A, act (g₁ * g₂) A = act g₁ (act g₂ A))
  (hact_one : ∀ A, act 1 A = A)
  (hA₀_in_𝒜 : A₀ ∈ 𝒜)
  (hA₀_in_max : A₀ ∈ max_apts)
  (h𝒜_stable : ∀ g : G, ∀ A ∈ 𝒜, act g A ∈ 𝒜)
  (h𝒜_sub_max : 𝒜 ⊆ max_apts)
  (strong_transit_max : ∀ A' ∈ max_apts, ∃ g : G, act g A' = A₀) :
-- imply
  𝒜 = max_apts := by
-- proof
  ext A
  constructor
  · exact fun h => h𝒜_sub_max h
  · intro hA_max
    obtain ⟨g, hg⟩ := strong_transit_max A hA_max
    have hA_eq : A = act g⁻¹ A₀ := by
      have h1 : act g⁻¹ (act g A) = A := by rw [← hact_mul, inv_mul_cancel, hact_one]
      rw [← h1, hg]
    rw [hA_eq]
    exact h𝒜_stable g⁻¹ A₀ hA₀_in_𝒜

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[maximal_apt_system_slv_helper](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma maximal_apt_system_slv_helper
  {C : DVRContext}
  {α : SLVAction C}
  {𝒜 : Set (Set (Simplex C))}
  {max_apts : Set (Set (Simplex C))}
  {A₀ : Set (Simplex C)}
-- given
  (hA₀_in_𝒜 : A₀ ∈ 𝒜)
  (hA₀_in_max : A₀ ∈ max_apts)
  (h𝒜_stable : ∀ g : SLV C, ∀ A ∈ 𝒜, α.act_apartment g A ∈ 𝒜)
  (h𝒜_sub_max : 𝒜 ⊆ max_apts)
  (strong_transit_max : ∀ A' ∈ max_apts, ∃ g : SLV C, α.act_apartment g A' = A₀) :
-- imply
  𝒜 = max_apts := by
-- proof
  ext A
  constructor
  · exact fun h => h𝒜_sub_max h
  · intro hA_max
    obtain ⟨g, hg⟩ := strong_transit_max A hA_max
    have hA_eq : A = α.act_apartment g⁻¹ A₀ := by
      rw [← hg, α.act_apartment_eq, α.act_apartment_eq]
      ext σ
      simp only [Set.mem_image]
      constructor
      · intro hσ
        exact ⟨α.act_simplex g σ, ⟨σ, hσ, rfl⟩,
          by rw [← α.act_mul, inv_mul_cancel, α.act_one]⟩
      · rintro ⟨τ, ⟨σ', hσ', rfl⟩, hτ'⟩
        have : σ' = σ := by
          have h1 : σ' = α.act_simplex (g⁻¹ * g) σ' := by
            rw [inv_mul_cancel, α.act_one]
          rw [α.act_mul] at h1
          exact h1.trans hτ'
        rwa [← this]
    rw [hA_eq]
    exact h𝒜_stable g⁻¹ A₀ hA₀_in_𝒜

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[frame_apartment_mem_frameApartmentSystem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma frame_apartment_mem_frameApartmentSystem
  {C : DVRContext}
  {F : Frame C} :
-- imply
  Apartment C F ∈ frameApartmentSystem C :=
-- proof
  ⟨F, rfl⟩

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[frame_apartment_system_stable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma frame_apartment_system_stable
  {C : DVRContext}
  [TopologicalSpace C.k]
  [IsDiscreteValuationRing C.𝔬]
  [LocallyCompactSpace C.k]
  {α : SLVAction C}
-- given
  (ho_complete : IsAdicComplete (DVRContext.maxIdeal C) C.𝔬) :
-- imply
  ∀ g : SLV C, ∀ A ∈ frameApartmentSystem C, α.act_apartment g A ∈ frameApartmentSystem C := by
-- proof
  intro g A ⟨F, hF⟩
  rw [hF, α.act_apartment_frame_compat g F]
  exact ⟨α.act_frame g F, rfl⟩

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[frame_apartment_system_sub_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma frame_apartment_system_sub_maximal
  {C : DVRContext}
  {max_apts : Set (Set (Simplex C))}
-- given
  (hframes : ∀ F : Frame C, Apartment C F ∈ max_apts) :
-- imply
  frameApartmentSystem C ⊆ max_apts := by
-- proof
  intro A ⟨F, hF⟩
  rw [hF]
  exact hframes F

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[strong_transitivity_from_compact_open_iwahori](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma strong_transitivity_from_compact_open_iwahori
  {C : DVRContext}
  [TopologicalSpace (Fin C.n → Fin C.n → C.𝔬)]
  {max_apts : Set (Set (Simplex C))}
-- given
  (_hB_open : IsOpen (IwahoriSubgroup C))
  (_hB_compact : IsCompact (IwahoriSubgroup C))
  (hframes : ∀ F : Frame C, Apartment C F ∈ max_apts)
  (hmax : IsMaximalApartmentSystem C max_apts) :
-- imply
  ∃ (max_apts' : Set (Set (Simplex C))), (∀ F : Frame C, Apartment C F ∈ max_apts') ∧ (∀ σ τ : Simplex C, σ.IsMaximal C → τ.IsMaximal C → ∃ A ∈ max_apts', σ ∈ A ∧ τ ∈ A) :=
-- proof
⟨max_apts, hframes, fun σ τ hσ _hτ => hmax.1.2.1 σ τ⟩

end AffineBuildingSLVStrong

namespace AffineBuildingSLVStrong

/--
[slv_maximal_apartment_system](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
lemma slv_maximal_apartment_system
  {C : DVRContext}
  [TopologicalSpace (Fin C.n → Fin C.n → C.𝔬)]
  {K : Set (Fin C.n → Fin C.n → C.𝔬)}
  {max_apts : Set (Set (Simplex C))}
-- given
  (hB_open : IsOpen (IwahoriSubgroup C))
  (hBruhat : ∃ (I : Type*) (cells : I → Set (Fin C.n → Fin C.n → C.𝔬)), (∀ i, IsOpen (cells i)) ∧ Set.univ = ⋃ i, cells i ∧ (∀ i j, i ≠ j → Disjoint (cells i) (cells j)) ∧ ∃ i₀, cells i₀ = IwahoriSubgroup C)
  (hBK : IwahoriSubgroup C ⊆ K)
  (hK : IsCompact K)
  (hframes : ∀ F : Frame C, Apartment C F ∈ max_apts)
  (hmax : IsMaximalApartmentSystem C max_apts) :
-- imply
  IsClosed (IwahoriSubgroup C) ∧ IsCompact (IwahoriSubgroup C) ∧ ∃ (max_apts' : Set (Set (Simplex C))), (∀ F : Frame C, Apartment C F ∈ max_apts') ∧ (∀ σ τ : Simplex C, σ.IsMaximal C → τ.IsMaximal C → ∃ A ∈ max_apts', σ ∈ A ∧ τ ∈ A) := by
-- proof
  have hclosed : IsClosed (IwahoriSubgroup C) :=
    open_plus_decomp_implies_closed (IwahoriSubgroup C) hB_open hBruhat
  have hcompact : IsCompact (IwahoriSubgroup C) :=
    closed_in_compact_is_compact (IwahoriSubgroup C) K hclosed hBK hK
  refine ⟨hclosed, hcompact, ?_⟩
  exact strong_transitivity_from_compact_open_iwahori C hB_open hcompact
    max_apts hframes hmax

end AffineBuildingSLVStrong

/--
[stdBasisVec_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
private lemma stdBasisVec_ne_zero_eq
  {C : DVRContext}
  {j : Fin C.n} :
-- imply
  stdBasisVec C j ≠ 0 := by
-- proof
  apply AffineBuildingSLVStrong.stdBasisVec_ne_zero C j

/--
[sum_std_basis_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
private lemma sum_std_basis_apply_eq
  {C : DVRContext}
  {coeffs : Fin C.n → C.k}
  {i : Fin C.n} :
-- imply
  (∑ j, coeffs j * stdBasisVec C j i) = coeffs i := by
-- proof
  apply AffineBuildingSLVStrong.sum_std_basis_apply C coeffs i

/--
[sum_std_basis_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLVStrong.lean)
-/
@[path]
private lemma sum_std_basis_eq_eq
  {C : DVRContext}
  {coeffs : Fin C.n → C.k} :
-- imply
  (fun i => ∑ j, coeffs j * stdBasisVec C j i) = coeffs := by
-- proof
  apply AffineBuildingSLVStrong.sum_std_basis_eq C coeffs


-- created on 2026-10-23
