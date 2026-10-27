import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private abbrev v2 {α : Type} (a b : α) : Fin 2 → α := Matrix.vecCons a (Matrix.vecCons b Matrix.vecEmpty)

private abbrev m2 {α : Type} (a b c d : α) : Matrix (Fin 2) (Fin 2) α := Matrix.vecCons (v2 a b) (Matrix.vecCons (v2 c d) Matrix.vecEmpty)


/--
[CerednikDrinfeld_SpecialModule_exists_forall_apply_eq_mul_dotProduct_mulVec_of_forall_apply_mulVec_eq_apply_inv_mul_adjugate_mul_mulVec](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_SpecialModule_exists_forall_apply_eq_mul_dotProduct_mulVec_of_forall_apply_mulVec_eq_apply_inv_mul_adjugate_mul_mulVec.lean)
-/
@[path]
private lemma main
  {k : Type} [Field k]
  {μ : Matrix (Fin 2) (Fin 2) k}
  {b : (Fin 2 → k) →ₗ[k] (Fin 2 → k) →ₗ[k] k}
  -- given
  (_ : μ.trace = 0)
  (hdet : μ.det ≠ 0)
  (hb : ∀ (x : Matrix (Fin 2) (Fin 2) k) (v w : Fin 2 → k), b (x.mulVec v) w = b v ((μ⁻¹ * x.adjugate * μ).mulVec w)) :
  -- imply
  ∃ c : k, ∀ v w : Fin 2 → k, b v w = c * dotProduct v ((m2 0 1 (-1) 0 * μ).mulVec w) := by
  -- proof
  classical
  have hμu : IsUnit μ.det := Iff.mpr isUnit_iff_ne_zero hdet
  have hμinv : ∀ z : Fin 2 → k, μ.mulVec (μ⁻¹.mulVec z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hμu, Matrix.one_mulVec]
  have key : ∀ (A : Matrix (Fin 2) (Fin 2) k) (v w : Fin 2 → k), b (A.mulVec v) w = b v (μ⁻¹.mulVec (A.adjugate.mulVec (μ.mulVec w))) := by
    intro A v w
    rw [hb, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hmv : ∀ (A : Matrix (Fin 2) (Fin 2) k) (z : Fin 2 → k) (i : Fin 2), A.mulVec z i = A i 0 * z 0 + A i 1 * z 1 := by
    intro A z i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hv0 : ∀ c : k, (v2 0 c : Fin 2 → k) = c • v2 0 1 := fun c => by
    ext i
    fin_cases i
    · simp
    · simp
  have hv1 : ∀ c : k, (v2 c 0 : Fin 2 → k) = c • v2 1 0 := fun c => by
    ext i
    fin_cases i
    · simp
    · simp
  have hA00v : ∀ v : Fin 2 → k, (m2 (1 : k) 0 0 0).mulVec v = v2 (v 0) 0 := fun v => by
    ext i
    fin_cases i
    · simp [hmv]
    · simp [hmv]
  have hA11v : ∀ v : Fin 2 → k, (m2 (0 : k) 0 0 1).mulVec v = v2 0 (v 1) := fun v => by
    ext i
    fin_cases i
    · simp [hmv]
    · simp [hmv]
  have hA01v : ∀ v : Fin 2 → k, (m2 (0 : k) 1 0 0).mulVec v = v2 (v 1) 0 := fun v => by
    ext i
    fin_cases i
    · simp [hmv]
    · simp [hmv]
  have hA01nv : ∀ v : Fin 2 → k, (m2 (0 : k) (-1) 0 0).mulVec v = v2 (-v 1) 0 := fun v => by
    ext i
    fin_cases i
    · simp [hmv]
    · simp [hmv]
  have hadj00 : (m2 (1 : k) 0 0 0).adjugate = m2 (0 : k) 0 0 1 := by
    rw [Matrix.adjugate_fin_two_of]
    norm_num
  have hadj11 : (m2 (0 : k) 0 0 1).adjugate = m2 (1 : k) 0 0 0 := by
    rw [Matrix.adjugate_fin_two_of]
    norm_num
  have hadj01 : (m2 (0 : k) 1 0 0).adjugate = m2 (0 : k) (-1) 0 0 := by
    rw [Matrix.adjugate_fin_two_of]
    norm_num
  set u₀ : Fin 2 → k := μ⁻¹.mulVec (v2 1 0)
  set u₁ : Fin 2 → k := μ⁻¹.mulVec (v2 0 1)
  set α : k := b (v2 1 0) u₁
  set β : k := b (v2 0 1) u₀
  have hE3 : ∀ w, b (v2 1 0) w = (μ.mulVec w) 1 * α := by
    intro w
    have h := key (m2 (1 : k) 0 0 0) (v2 1 0) w
    rw [hadj00, hA00v, hA11v, hv0 ((μ.mulVec w) 1), Matrix.mulVec_smul, map_smul, smul_eq_mul] at h
    simp only [Matrix.cons_val_zero] at h
    apply h
  have hE4 : ∀ w, b (v2 0 1) w = (μ.mulVec w) 0 * β := by
    intro w
    have h := key (m2 (0 : k) 0 0 1) (v2 0 1) w
    rw [hadj11, hA11v, hA00v, hv1 ((μ.mulVec w) 0), Matrix.mulVec_smul, map_smul, smul_eq_mul] at h
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at h
    apply h
  have hE5 : ∀ w, b (v2 1 0) w = -(μ.mulVec w) 1 * β := by
    intro w
    have h := key (m2 (0 : k) 1 0 0) (v2 0 1) w
    rw [hadj01, hA01v, hA01nv, hv1 (-(μ.mulVec w) 1), Matrix.mulVec_smul, map_smul, smul_eq_mul] at h
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at h
    apply h
  have hαβ : α = -β := by
    have h3 := hE3 <| μ⁻¹.mulVec (v2 0 1)
    have h5 := hE5 <| μ⁻¹.mulVec (v2 0 1)
    rw [hμinv] at h3 h5
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, one_mul, neg_mul] at h3 h5
    rw [← h3, h5]
  have hbv : ∀ x y : Fin 2 → k, b x y = x 0 * b (v2 1 0) y + x 1 * b (v2 0 1) y := by
    intro x y
    have hx : x = x 0 • v2 1 0 + x 1 • v2 0 1 := by
      ext i
      fin_cases i
      · simp
      · simp
    conv_lhs => rw [hx]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  have hJ : ∀ w : Fin 2 → k, (m2 (0 : k) 1 (-1) 0 * μ).mulVec w = v2 ((μ.mulVec w) 1) (-(μ.mulVec w) 0) := by
    intro w
    rw [← Matrix.mulVec_mulVec]
    ext i
    fin_cases i
    · simp [hmv]
    · simp [hmv]
  refine ⟨α, fun v w => ?_⟩
  rw [hbv v w, hE3, hE4, hJ]
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [hαβ]
  ring


-- created on 2026-10-20
