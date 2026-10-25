import Lemma.AutomorphicForm.ArchType

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField IsDedekindDomain Matrix

open scoped Classical

namespace AutomorphicForm

section DetOneSubgroup

variable (K : Type*) [NormedField K]

def rowIsometrySubgroup₀ : Subgroup (GL (Fin 2) K) :=
  (Matrix.GeneralLinearGroup.det).ker ⊓ rowIsometrySubgroup K

theorem mem_rowIsometrySubgroup₀_iff {k : GL (Fin 2) K} :
    k ∈ rowIsometrySubgroup₀ K ↔
      (k : Matrix (Fin 2) (Fin 2) K).det = 1 ∧ IsRowIsometry k := by
  unfold rowIsometrySubgroup₀
  constructor
  · rintro ⟨hd, hi⟩
    exact ⟨Units.val_eq_one.mpr hd, hi⟩
  · rintro ⟨hd, hi⟩
    refine ⟨?_, hi⟩
    ext; exact hd

theorem rowIsometrySubgroup₀_le :
    rowIsometrySubgroup₀ K ≤ rowIsometrySubgroup K := inf_le_right

theorem weyl_mem_rowIsometrySubgroup₀ :
    (Matrix.GeneralLinearGroup.mk'' (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K)
      (by rw [Matrix.det_fin_two_of]; norm_num) : GL (Fin 2) K)
      ∈ rowIsometrySubgroup₀ K := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨?_, weyl_mem_rowIsometrySubgroup⟩
  show (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1
  rw [Matrix.det_fin_two_of]; ring

end DetOneSubgroup

section WeightChar

theorem entries_of_mem_rowIsometrySubgroup₀ {k : GL (Fin 2) ℝ}
    (hk : k ∈ rowIsometrySubgroup₀ ℝ) :
    let a := (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0
    let b := (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1
    (k : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -b ∧
      (k : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = a ∧ a ^ 2 + b ^ 2 = 1 := by
  obtain ⟨hd, hdn, hiso⟩ := (mem_rowIsometrySubgroup₀_iff ℝ).mp hk
  set a := (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0
  set b := (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1
  set c := (k : Matrix (Fin 2) (Fin 2) ℝ) 1 0
  set d := (k : Matrix (Fin 2) (Fin 2) ℝ) 1 1
  have h10 : a ^ 2 + b ^ 2 = 1 := by
    have := hiso 1 0
    simp only [one_mul, zero_mul, add_zero, Real.norm_eq_abs, sq_abs, norm_one,
      one_pow, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at this
    linarith
  have h01 : c ^ 2 + d ^ 2 = 1 := by
    have := hiso 0 1
    simp only [zero_mul, one_mul, zero_add, Real.norm_eq_abs, sq_abs, norm_one,
      one_pow, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at this
    linarith
  have h11 : a * c + b * d = 0 := by
    have h1 := hiso 1 1
    simp only [one_mul, Real.norm_eq_abs, sq_abs, norm_one, one_pow] at h1
    nlinarith [h10, h01]
  have hdet : a * d - b * c = 1 := by
    have := hd; rw [Matrix.det_fin_two] at this; linarith

  refine ⟨?_, ?_, h10⟩
  · nlinarith [sq_nonneg (a - d), sq_nonneg (b + c), h10, h01, h11, hdet]
  · nlinarith [sq_nonneg (a - d), sq_nonneg (b + c), h10, h01, h11, hdet]

def firstRowℂ (k : GL (Fin 2) ℝ) : ℂ :=
  ⟨(k : Matrix (Fin 2) (Fin 2) ℝ) 0 0, (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1⟩

theorem normSq_firstRowℂ_of_mem {k : GL (Fin 2) ℝ}
    (hk : k ∈ rowIsometrySubgroup₀ ℝ) :
    Complex.normSq (firstRowℂ k) = 1 := by
  obtain ⟨_, _, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ hk
  simp only [firstRowℂ, Complex.normSq_mk]
  nlinarith

theorem firstRowℂ_ne_zero_of_mem {k : GL (Fin 2) ℝ}
    (hk : k ∈ rowIsometrySubgroup₀ ℝ) :
    firstRowℂ k ≠ 0 := fun h0 => by
  have h := normSq_firstRowℂ_of_mem hk
  rw [h0, map_zero] at h
  exact one_ne_zero h.symm

theorem firstRowℂ_mul_of_mem {k k' : GL (Fin 2) ℝ}
    (hk' : k' ∈ rowIsometrySubgroup₀ ℝ) :
    firstRowℂ (k * k') = firstRowℂ k * firstRowℂ k' := by
  obtain ⟨hc', hd', _⟩ := entries_of_mem_rowIsometrySubgroup₀ hk'
  apply Complex.ext
  · show ((k * k' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = _
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hc',
      Complex.mul_re, firstRowℂ, firstRowℂ]
    ring
  · show ((k * k' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = _
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hd',
      Complex.mul_im, firstRowℂ, firstRowℂ]

noncomputable def archWeightOneℝ : rowIsometrySubgroup₀ ℝ →* ℂˣ where
  toFun k := Units.mk0 (firstRowℂ (k : GL (Fin 2) ℝ))
    (firstRowℂ_ne_zero_of_mem k.2)
  map_one' := Units.ext <| Complex.ext (by simp [firstRowℂ]) (by simp [firstRowℂ])
  map_mul' k k' := by
    ext
    exact firstRowℂ_mul_of_mem k'.2

noncomputable def archWeightCharℝ (n : ℤ) : rowIsometrySubgroup₀ ℝ →* ℂˣ :=
  (zpowGroupHom n).comp archWeightOneℝ

theorem archWeightOneℝ_weyl :
    (archWeightOneℝ
      ⟨_, weyl_mem_rowIsometrySubgroup₀ ℝ⟩ : ℂ) = ⟨0, 1⟩ := by
  show firstRowℂ _ = (⟨0, 1⟩ : ℂ)
  apply Complex.ext <;> simp [firstRowℂ]

theorem archWeightOneℝ_ne_one :
    archWeightOneℝ ⟨_, weyl_mem_rowIsometrySubgroup₀ ℝ⟩ ≠ 1 := by
  intro h
  have : (⟨0, 1⟩ : ℂ) = 1 := archWeightOneℝ_weyl ▸ (Units.val_eq_one.mpr h)
  simp [Complex.ext_iff] at this

end WeightChar

section PredicateZero

variable (F : Type) [Field F] [NumberField F]

def HasArchCharacterAt₀ (w : InfinitePlace F) (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ k : rowIsometrySubgroup₀ w.Completion, ∀ g : AdelicGL2 (𝓞 F) F,
    φ (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion))
      = (χ k : ℂ) * φ g

def HasArchType₀ (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ w : InfinitePlace F, HasArchCharacterAt₀ F w (χ w) φ

theorem hasArchType₀_of_hasArchType
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (h : HasArchType F χ φ) :
    HasArchType₀ F
      (fun w => (χ w).comp (Subgroup.inclusion (rowIsometrySubgroup₀_le w.Completion))) φ :=
  fun w k g => h w (Subgroup.inclusion (rowIsometrySubgroup₀_le _) k) g

theorem hasArchType₀_zero
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ) :
    HasArchType₀ F χ (fun _ => 0) := fun _ _ _ => by simp

theorem hasArchType₀_const_of_trivial (c : ℂ) :
    HasArchType₀ F (fun _ => 1) (fun _ => c) := fun _ _ _ => (one_mul c).symm

theorem not_hasArchCharacterAt₀_one_of_ne_one (w : InfinitePlace F)
    (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (k : rowIsometrySubgroup₀ w.Completion) (hχ : χ k ≠ 1) :
    ¬ HasArchCharacterAt₀ F w χ (fun _ => 1) := fun h => by
  have hk := h k 1
  simp only [mul_one] at hk
  exact hχ (Units.val_eq_one.mp hk.symm)

end PredicateZero

section Ed9Witness

example : (HasArchType₀ ℚ (fun _ => 1) (fun _ => (1 : ℂ))) ∧
    Nonempty (InfinitePlace ℚ) ∧
    ∀ w : InfinitePlace ℚ, Nonempty (rowIsometrySubgroup₀ w.Completion) :=
  ⟨hasArchType₀_const_of_trivial ℚ 1, ⟨Rat.infinitePlace⟩, fun _ => ⟨1⟩⟩

end Ed9Witness

end AutomorphicForm
