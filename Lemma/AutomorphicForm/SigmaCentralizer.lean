import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group
import Def.AutomorphicForm_SigmaCentralizer

set_option autoImplicit false

namespace AutomorphicForm

variable {G : Type*} [Group G]


@[simp] theorem mem_sigmaCentralizer_iff {σ : G →* G} {δ t : G} :
    t ∈ sigmaCentralizer σ δ ↔ t * δ * (σ t)⁻¹ = δ := Iff.rfl

theorem mem_sigmaCentralizer_iff_fixed {σ : G →* G} {δ t : G} :
    t ∈ sigmaCentralizer σ δ ↔ δ * σ t * δ⁻¹ = t := by
  rw [mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem mem_sigmaCentralizer_iff_inv {σ : G →* G} {δ t : G} :
    t ∈ sigmaCentralizer σ δ ↔ t⁻¹ * δ * σ t = δ := by
  rw [mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul, mul_assoc, inv_mul_eq_iff_eq_mul]
  exact eq_comm

theorem sigmaCentralizer_id (δ : G) :
    sigmaCentralizer (MonoidHom.id G) δ = Subgroup.centralizer {δ} := by
  ext t
  rw [mem_sigmaCentralizer_iff, Subgroup.mem_centralizer_singleton_iff, MonoidHom.id_apply,
    mul_inv_eq_iff_eq_mul]

theorem sigmaCentralizer_one_eq_bot (δ : G) :
    sigmaCentralizer (1 : G →* G) δ = ⊥ := by
  ext t
  rw [mem_sigmaCentralizer_iff, Subgroup.mem_bot]
  constructor
  · intro h
    have h1 : t * δ = δ := by
      simpa using h
    exact mul_right_cancel (by rw [one_mul]; exact h1)
  · rintro rfl
    simp

end
