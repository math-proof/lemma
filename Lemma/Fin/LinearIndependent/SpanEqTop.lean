import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AutomorphicForm_linearIndependent_mulVec_and_span_eq_top_of_forall_isUnit_of_card_eq_four](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AutomorphicForm_linearIndependent_mulVec_and_span_eq_top_of_forall_isUnit_of_card_eq_four.lean)
-/
@[path]
private lemma main
    (K L : Type) [Field K] [Field L] [Algebra K L] (h2 : Module.finrank K L = 2)
    (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L)
    (ι : Type) [Fintype ι] (hcard : Fintype.card ι = 4)
    (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hspan : ∀ x : Matrix (Fin 2) (Fin 2) L,
      x * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * x.map σ ↔
        x ∈ Submodule.span K (Set.range b))
    (hdiv : ∀ x : Matrix (Fin 2) (Fin 2) L,
      x * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * x.map σ → x ≠ 0 → IsUnit x)
    (v : Fin 2 → L) (hv : v ≠ 0) :
    LinearIndependent K (fun i => (b i).mulVec v) ∧
      Submodule.span K (Set.range fun i => (b i).mulVec v) = ⊤ := by
  classical
  let φ : Matrix (Fin 2) (Fin 2) L →ₗ[K] (Fin 2 → L) :=
    { toFun := fun x => x.mulVec v
      map_add' := fun x y => Matrix.add_mulVec x y v
      map_smul' := fun k x => Matrix.smul_mulVec k x v }
  have hφ : ∀ x, φ x = x.mulVec v := fun _ => rfl
  have hinj : ∀ x ∈ Submodule.span K (Set.range b), φ x = 0 → x = 0 := by
    intro x hx hx0
    by_contra hne
    have hu : IsUnit x := hdiv x ((hspan x).2 hx) hne
    obtain ⟨ux, rfl⟩ := hu
    apply hv
    have : (ux : Matrix (Fin 2) (Fin 2) L).mulVec v = 0 := hx0
    have := congrArg (fun w => ((ux⁻¹ : (Matrix (Fin 2) (Fin 2) L)ˣ) : Matrix (Fin 2) (Fin 2) L).mulVec w) this
    simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] using this
  have hli : LinearIndependent K (fun i => (b i).mulVec v) := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    have hmem : ∑ j ∈ s, g j • b j ∈ Submodule.span K (Set.range b) :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hzero : φ (∑ j ∈ s, g j • b j) = 0 := by
      rw [map_sum]
      simp only [hφ, Matrix.smul_mulVec]
      exact hsum
    exact (linearIndependent_iff'.1 hb) s g (hinj _ hmem hzero) i hi
  let _ : Module.Finite K L := Module.finite_of_finrank_eq_succ h2
  have hrank : Module.finrank K (Fin 2 → L) = 4 := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, h2, smul_eq_mul]
  have hι : Nonempty ι := by
    rw [← Fintype.card_pos_iff, hcard]; exact Nat.succ_pos 3
  refine ⟨hli, ?_⟩
  exact hli.span_eq_top_of_card_eq_finrank (hcard.trans hrank.symm)

-- created on 2026-10-20
