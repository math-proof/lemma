import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct
open LinearMap


/--
No-cloning theorem (linear form): if a module over a field admits two linearly independent
vectors, there is no `K`-linear map `U : H ⊗ H → H ⊗ H` that clones every vector into a fixed
blank factor, i.e. `U (x ⊗ₜ e) = x ⊗ₜ x` for all `x`.
-/
@[path]
private lemma main
  [Field K]
  [AddCommGroup H]
  [Module K H]
  {ψ φ : H}
-- given
  (h : LinearIndependent K ![ψ, φ])
  (e : H) :
-- imply
  ¬ ∃ (U : H ⊗[K] H →ₗ[K] H ⊗[K] H),
    ∀ x : H, U (x ⊗ₜ[K] e) = x ⊗ₜ[K] x := by
-- proof
  rintro ⟨U, hU⟩
  have hT : LinearIndependent K
    (fun i : Fin 2 × Fin 2 ↦ (![ψ, φ] i.1) ⊗ₜ[K] (![ψ, φ] i.2)) :=
    h.tmul_of_isDomain h
  have hsum :
    ψ ⊗ₜ[K] ψ + φ ⊗ₜ[K] φ =
      (ψ + φ) ⊗ₜ[K] (ψ + φ) := calc
    _ = U (ψ ⊗ₜ[K] e) + U (φ ⊗ₜ[K] e) := by
      rw [hU, hU]
    _ = U (ψ ⊗ₜ[K] e + φ ⊗ₜ[K] e) := by
      rw [map_add]
    _ = U ((ψ + φ) ⊗ₜ[K] e) := by
      rw [TensorProduct.add_tmul]
    _ = (ψ + φ) ⊗ₜ[K] (ψ + φ) :=
      hU _
  have hexpand :
    (ψ + φ) ⊗ₜ[K] (ψ + φ) =
      ψ ⊗ₜ[K] ψ + ψ ⊗ₜ[K] φ + φ ⊗ₜ[K] ψ + φ ⊗ₜ[K] φ := by
    rw [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.tmul_add]
    abel
  have hcross : ψ ⊗ₜ[K] φ + φ ⊗ₜ[K] ψ = 0 := by
    have h' : φ ⊗ₜ[K] φ = ψ ⊗ₜ[K] φ + φ ⊗ₜ[K] ψ + φ ⊗ₜ[K] φ :=
      add_left_cancel (hsum.trans hexpand)
    apply add_eq_right.mp
    apply h'.symm
  set l :=
    Finsupp.single ((0 : Fin 2), (1 : Fin 2)) (1 : K) +
      Finsupp.single ((1 : Fin 2), (0 : Fin 2)) (1 : K)
  have hl :
    Finsupp.linearCombination K
      (fun i : Fin 2 × Fin 2 ↦ (![ψ, φ] i.1) ⊗ₜ[K] (![ψ, φ] i.2)) l = 0 := by
    simp [l, Finsupp.linearCombination_single, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_smul, hcross]
  apply absurd
  ·
    apply (linearIndependent_iff.1 hT) l
    apply hl
  ·
    intro h0
    have : (l (0, 1) : K) = 0 := by
      rw [h0]
      rfl
    simp [l] at this


-- created on 2026-11-09
-- updated on 2026-11-10
