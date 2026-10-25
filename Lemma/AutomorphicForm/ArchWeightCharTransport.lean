import Lemma.AutomorphicForm.ArchWeightChar

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField IsDedekindDomain Matrix
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

open scoped Classical

namespace AutomorphicForm

section Furniture

variable {K L : Type*} [NormedField K] [NormedField L]

noncomputable def glEquivOfRingEquiv (e : K ≃+* L) : GL (Fin 2) K ≃* GL (Fin 2) L :=
  Units.mapEquiv (RingEquiv.mapMatrix (m := Fin 2) e).toMulEquiv

theorem glEquivOfRingEquiv_apply_entry (e : K ≃+* L) (k : GL (Fin 2) K) (i j : Fin 2) :
    ((glEquivOfRingEquiv e k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
      = e ((k : Matrix (Fin 2) (Fin 2) K) i j) := rfl

theorem map_mem_rowIsometrySubgroup₀_of_normPreserving (e : K ≃+* L)
    (he : ∀ x : K, ‖e x‖ = ‖x‖) (k : GL (Fin 2) K)
    (hk : k ∈ rowIsometrySubgroup₀ K) :
    glEquivOfRingEquiv e k ∈ rowIsometrySubgroup₀ L := by
  obtain ⟨hd, hnd, hiso⟩ := (mem_rowIsometrySubgroup₀_iff K).mp hk
  have hdL : ((glEquivOfRingEquiv e k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det = 1 := by
    change (RingEquiv.mapMatrix (m := Fin 2) e (k : Matrix (Fin 2) (Fin 2) K)).det = 1
    rw [← RingEquiv.map_det, hd, map_one]
  refine (mem_rowIsometrySubgroup₀_iff L).mpr ⟨hdL, ?_, ?_⟩
  · rw [hdL]; exact norm_one
  · intro x y
    have hes : ∀ z : L, ‖e.symm z‖ = ‖z‖ := fun z => by
      rw [← he (e.symm z), e.apply_symm_apply]
    have hent : ∀ i j, ((glEquivOfRingEquiv e k : GL (Fin 2) L) : Matrix _ _ L) i j
        = e ((k : Matrix (Fin 2) (Fin 2) K) i j) := fun i j => rfl
    simp only [hent]
    calc ‖x * e (k 0 0) + y * e (k 1 0)‖ ^ 2 + ‖x * e (k 0 1) + y * e (k 1 1)‖ ^ 2
        = ‖e (e.symm x * k 0 0 + e.symm y * k 1 0)‖ ^ 2
          + ‖e (e.symm x * k 0 1 + e.symm y * k 1 1)‖ ^ 2 := by
          simp only [map_add, map_mul, e.apply_symm_apply]
      _ = ‖e.symm x * k 0 0 + e.symm y * k 1 0‖ ^ 2
          + ‖e.symm x * k 0 1 + e.symm y * k 1 1‖ ^ 2 := by rw [he, he]
      _ = ‖e.symm x‖ ^ 2 + ‖e.symm y‖ ^ 2 := hiso (e.symm x) (e.symm y)
      _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by rw [hes, hes]

noncomputable def rowIsometrySubgroup₀Map (e : K ≃+* L)
    (he : ∀ x : K, ‖e x‖ = ‖x‖) :
    rowIsometrySubgroup₀ K →* rowIsometrySubgroup₀ L where
  toFun k := ⟨glEquivOfRingEquiv e k, map_mem_rowIsometrySubgroup₀_of_normPreserving e he k k.2⟩
  map_one' := by ext; simp [glEquivOfRingEquiv]
  map_mul' k k' := by ext; simp [glEquivOfRingEquiv]

theorem rowIsometrySubgroup₀Map_weyl (e : K ≃+* L) (he : ∀ x : K, ‖e x‖ = ‖x‖) :
    rowIsometrySubgroup₀Map e he ⟨_, weyl_mem_rowIsometrySubgroup₀ K⟩
      = ⟨_, weyl_mem_rowIsometrySubgroup₀ L⟩ := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rowIsometrySubgroup₀Map, glEquivOfRingEquiv_apply_entry,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, map_zero, map_one, map_neg]

end Furniture

section RealPlace

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in

theorem norm_ringEquivRealOfIsReal {w : InfinitePlace F} (hw : w.IsReal) (x : w.Completion) :
    ‖ringEquivRealOfIsReal hw x‖ = ‖x‖ :=
  (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) x

noncomputable def archWeightOneAt {w : InfinitePlace F} (hw : w.IsReal) :
    rowIsometrySubgroup₀ w.Completion →* ℂˣ :=
  archWeightOneℝ.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
    (norm_ringEquivRealOfIsReal hw))

noncomputable def archWeightCharAt {w : InfinitePlace F} (hw : w.IsReal) (n : ℤ) :
    rowIsometrySubgroup₀ w.Completion →* ℂˣ :=
  (zpowGroupHom n).comp (archWeightOneAt hw)

omit [NumberField F] in

theorem archWeightOneAt_weyl_ne_one {w : InfinitePlace F} (hw : w.IsReal) :
    archWeightOneAt hw ⟨_, weyl_mem_rowIsometrySubgroup₀ w.Completion⟩ ≠ 1 := by
  unfold archWeightOneAt
  rw [MonoidHom.comp_apply, rowIsometrySubgroup₀Map_weyl]
  exact archWeightOneℝ_ne_one

omit [NumberField F] in

theorem archWeightOneAt_ne_one {w : InfinitePlace F} (hw : w.IsReal) :
    archWeightOneAt hw ≠ 1 := fun h =>
  archWeightOneAt_weyl_ne_one hw (h ▸ rfl)

end RealPlace

section Family

variable (F : Type) [Field F] [NumberField F]

open scoped Classical in

noncomputable def archWeightCharFamily (n : ℤ) :
    ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ :=
  fun w => if hw : w.IsReal then archWeightCharAt hw n else 1

omit [NumberField F] in
theorem archWeightCharFamily_apply_of_isReal (n : ℤ) {w : InfinitePlace F} (hw : w.IsReal) :
    archWeightCharFamily F n w = archWeightCharAt hw n := dif_pos hw

omit [NumberField F] in
theorem archWeightCharFamily_apply_of_isComplex (n : ℤ) {w : InfinitePlace F}
    (hw : w.IsComplex) : archWeightCharFamily F n w = 1 :=
  dif_neg (by rwa [← not_isReal_iff_isComplex] at hw)

example : HasArchType₀ F (archWeightCharFamily F 1) (fun _ => 0) :=
  hasArchType₀_zero F (archWeightCharFamily F 1)

theorem archWeightCharFamily_rat_one_ne_one :
    archWeightCharFamily ℚ 1 Rat.infinitePlace ≠ 1 := by
  rw [archWeightCharFamily_apply_of_isReal ℚ 1 Rat.isReal_infinitePlace]
  intro h
  have := DFunLike.congr_fun h ⟨_, weyl_mem_rowIsometrySubgroup₀ _⟩
  simp only [archWeightCharAt, MonoidHom.comp_apply, zpowGroupHom_apply, zpow_one,
    MonoidHom.one_apply] at this
  exact archWeightOneAt_weyl_ne_one Rat.isReal_infinitePlace this

end Family

end AutomorphicForm
