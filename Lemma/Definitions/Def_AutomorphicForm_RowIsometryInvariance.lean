import Lemma.Definitions.Def_AutomorphicForm_WindowedSiegelSet

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

namespace WindowedSiegel

open NumberField.AdelicLevel

variable {K : Type*} [NormedField K]

def IsRowIsometry (k : GL (Fin 2) K) : Prop :=
  ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1 ∧
    ∀ x y : K,
      ‖x * (k : Matrix (Fin 2) (Fin 2) K) 0 0 + y * (k : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
        + ‖x * (k : Matrix (Fin 2) (Fin 2) K) 0 1
            + y * (k : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2

theorem isRowIsometry_one : IsRowIsometry (1 : GL (Fin 2) K) := by
  constructor
  · simp
  · intro x y
    have h00 : (1 : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := Matrix.one_apply_eq 0
    have h11 : (1 : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := Matrix.one_apply_eq 1
    have h10 : (1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := Matrix.one_apply_ne (by decide)
    have h01 : (1 : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := Matrix.one_apply_ne (by decide)
    show ‖x * (1 : Matrix (Fin 2) (Fin 2) K) 0 0 + y * (1 : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
        + ‖x * (1 : Matrix (Fin 2) (Fin 2) K) 0 1 + y * (1 : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2
    rw [h00, h11, h10, h01, mul_one, mul_one, mul_zero, mul_zero, add_zero, zero_add]

theorem IsRowIsometry.mul {k k' : GL (Fin 2) K} (hk : IsRowIsometry k)
    (hk' : IsRowIsometry k') : IsRowIsometry (k * k') := by
  obtain ⟨hdet, hrow⟩ := hk
  obtain ⟨hdet', hrow'⟩ := hk'
  have hcoe : ((k * k' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (k : Matrix (Fin 2) (Fin 2) K) * (k' : Matrix (Fin 2) (Fin 2) K) := rfl
  constructor
  · rw [hcoe, Matrix.det_mul, norm_mul, hdet, hdet', one_mul]
  · intro x y
    have hentry : ∀ i : Fin 2,
        x * ((k : Matrix (Fin 2) (Fin 2) K) * (k' : Matrix (Fin 2) (Fin 2) K)) 0 i
          + y * ((k : Matrix (Fin 2) (Fin 2) K) * (k' : Matrix (Fin 2) (Fin 2) K)) 1 i
        = (x * (k : Matrix (Fin 2) (Fin 2) K) 0 0 + y * (k : Matrix (Fin 2) (Fin 2) K) 1 0)
              * (k' : Matrix (Fin 2) (Fin 2) K) 0 i
          + (x * (k : Matrix (Fin 2) (Fin 2) K) 0 1 + y * (k : Matrix (Fin 2) (Fin 2) K) 1 1)
              * (k' : Matrix (Fin 2) (Fin 2) K) 1 i := by
      intro i
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    show ‖x * ((k * k' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0
          + y * ((k * k' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
        + ‖x * ((k * k' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1
            + y * ((k * k' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2
    rw [hcoe, hentry 0, hentry 1,
      hrow' (x * (k : Matrix (Fin 2) (Fin 2) K) 0 0 + y * (k : Matrix (Fin 2) (Fin 2) K) 1 0)
        (x * (k : Matrix (Fin 2) (Fin 2) K) 0 1 + y * (k : Matrix (Fin 2) (Fin 2) K) 1 1),
      hrow x y]

theorem IsRowIsometry.inv {k : GL (Fin 2) K} (hk : IsRowIsometry k) :
    IsRowIsometry k⁻¹ := by
  obtain ⟨hdet, hrow⟩ := hk
  have hcoe : ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      * ((k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := Units.inv_mul k
  constructor
  · have hd : ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det
        * ((k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      rw [← Matrix.det_mul, hcoe, Matrix.det_one]
    have hnorm := congrArg norm hd
    rwa [norm_mul, hdet, mul_one, norm_one] at hnorm
  · intro x y
    set A := ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hA
    set B := ((k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hB
    have entry : ∀ i j : Fin 2,
        A i 0 * B 0 j + A i 1 * B 1 j = (1 : Matrix (Fin 2) (Fin 2) K) i j := by
      intro i j
      calc A i 0 * B 0 j + A i 1 * B 1 j
          = (A * B) i j := by rw [Matrix.mul_apply, Fin.sum_univ_two]
        _ = (1 : Matrix (Fin 2) (Fin 2) K) i j := by rw [hcoe]
    have e00 := entry 0 0
    have e01 := entry 0 1
    have e10 := entry 1 0
    have e11 := entry 1 1
    rw [Matrix.one_apply_eq] at e00 e11
    rw [Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] at e01
    rw [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e10
    have hwx : (x * A 0 0 + y * A 1 0) * B 0 0 + (x * A 0 1 + y * A 1 1) * B 1 0 = x := by
      calc (x * A 0 0 + y * A 1 0) * B 0 0 + (x * A 0 1 + y * A 1 1) * B 1 0
          = x * (A 0 0 * B 0 0 + A 0 1 * B 1 0) + y * (A 1 0 * B 0 0 + A 1 1 * B 1 0) := by
            ring
        _ = x * 1 + y * 0 := by rw [e00, e10]
        _ = x := by ring
    have hwy : (x * A 0 0 + y * A 1 0) * B 0 1 + (x * A 0 1 + y * A 1 1) * B 1 1 = y := by
      calc (x * A 0 0 + y * A 1 0) * B 0 1 + (x * A 0 1 + y * A 1 1) * B 1 1
          = x * (A 0 0 * B 0 1 + A 0 1 * B 1 1) + y * (A 1 0 * B 0 1 + A 1 1 * B 1 1) := by
            ring
        _ = x * 0 + y * 1 := by rw [e01, e11]
        _ = y := by ring
    have key := hrow (x * A 0 0 + y * A 1 0) (x * A 0 1 + y * A 1 1)
    rw [hwx, hwy] at key
    exact key.symm

variable (K)

def rowIsometrySubgroup : Subgroup (GL (Fin 2) K) where
  carrier := {k : GL (Fin 2) K | IsRowIsometry k}
  one_mem' := isRowIsometry_one
  mul_mem' := fun hk hk' => IsRowIsometry.mul hk hk'
  inv_mem' := fun hk => IsRowIsometry.inv hk

variable {K}

theorem mem_rowIsometrySubgroup_iff {k : GL (Fin 2) K} :
    k ∈ rowIsometrySubgroup K ↔ IsRowIsometry k := Iff.rfl

theorem topNormSq_mul_rowIsometry (g : GL (Fin 2) K) {k : GL (Fin 2) K}
    (hk : IsRowIsometry k) :
    topNormSq ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = topNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨-, hrow⟩ := hk
  have hcoe : ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (g : Matrix (Fin 2) (Fin 2) K) * (k : Matrix (Fin 2) (Fin 2) K) := rfl
  have htop : ∀ i : Fin 2,
      ((g : Matrix (Fin 2) (Fin 2) K) * (k : Matrix (Fin 2) (Fin 2) K)) 0 i
      = (g : Matrix (Fin 2) (Fin 2) K) 0 0 * (k : Matrix (Fin 2) (Fin 2) K) 0 i
        + (g : Matrix (Fin 2) (Fin 2) K) 0 1 * (k : Matrix (Fin 2) (Fin 2) K) 1 i := by
    intro i
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  unfold topNormSq
  rw [hcoe, htop 0, htop 1,
    hrow ((g : Matrix (Fin 2) (Fin 2) K) 0 0) ((g : Matrix (Fin 2) (Fin 2) K) 0 1)]

theorem rowNormSq_mul_rowIsometry (g : GL (Fin 2) K) {k : GL (Fin 2) K}
    (hk : IsRowIsometry k) :
    rowNormSq ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨-, hrow⟩ := hk
  have hcoe : ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (g : Matrix (Fin 2) (Fin 2) K) * (k : Matrix (Fin 2) (Fin 2) K) := rfl
  have hbot : ∀ i : Fin 2,
      ((g : Matrix (Fin 2) (Fin 2) K) * (k : Matrix (Fin 2) (Fin 2) K)) 1 i
      = (g : Matrix (Fin 2) (Fin 2) K) 1 0 * (k : Matrix (Fin 2) (Fin 2) K) 0 i
        + (g : Matrix (Fin 2) (Fin 2) K) 1 1 * (k : Matrix (Fin 2) (Fin 2) K) 1 i := by
    intro i
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  unfold rowNormSq
  rw [hcoe, hbot 0, hbot 1,
    hrow ((g : Matrix (Fin 2) (Fin 2) K) 1 0) ((g : Matrix (Fin 2) (Fin 2) K) 1 1)]

theorem localHeight_mul_rowIsometry (g : GL (Fin 2) K) {k : GL (Fin 2) K}
    (hk : IsRowIsometry k) : localHeight (g * k) = localHeight g := by
  have hdet := hk.1
  have hcoe : ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (g : Matrix (Fin 2) (Fin 2) K) * (k : Matrix (Fin 2) (Fin 2) K) := rfl
  unfold localHeight
  rw [rowNormSq_mul_rowIsometry g hk, hcoe, Matrix.det_mul, norm_mul, hdet, mul_one]

theorem xWindowSq_mul_rowIsometry (g : GL (Fin 2) K) {k : GL (Fin 2) K}
    (hk : IsRowIsometry k) : xWindowSq (g * k) = xWindowSq g := by
  unfold xWindowSq
  rw [topNormSq_mul_rowIsometry g hk, rowNormSq_mul_rowIsometry g hk,
    localHeight_mul_rowIsometry g hk]

theorem weyl_mem_rowIsometrySubgroup :
    (Matrix.GeneralLinearGroup.mk'' (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K)
      (by
        rw [Matrix.det_fin_two_of]
        norm_num) : GL (Fin 2) K) ∈ rowIsometrySubgroup K := by
  constructor
  · show ‖(!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).det‖ = 1
    rw [Matrix.det_fin_two_of]
    norm_num
  · intro x y
    have h00 : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 := rfl
    have h01 : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) 0 1 = 1 := rfl
    have h10 : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) 1 0 = -1 := rfl
    have h11 : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := rfl
    show ‖x * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) 0 0
          + y * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
        + ‖x * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) 0 1
            + y * (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2
    rw [h00, h01, h10, h11, mul_zero, mul_neg_one, zero_add, mul_one, mul_zero, add_zero,
      norm_neg]
    ring

section Adelic

variable (F : Type) [Field F] [NumberField F]

theorem archHeight_mul_rowIsometry (g : GL (Fin 2) (InfiniteAdeleRing F))
    {k : GL (Fin 2) (InfiniteAdeleRing F)}
    (hk : ∀ v : InfinitePlace F, IsRowIsometry (archComponent F v k)) :
    archHeight F (g * k) = archHeight F g := by
  unfold archHeight
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_mul, localHeight_mul_rowIsometry (archComponent F v g) (hk v)]

end Adelic

end WindowedSiegel

end AutomorphicForm

end
