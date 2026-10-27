import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Subalgebra_eq_top_of_associated_discr_of_basis](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Subalgebra_eq_top_of_associated_discr_of_basis.lean)
-/
@[path]
private lemma main
  {R A ι : Type} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] [Fintype ι] [DecidableEq ι]
  (b' : Module.Basis ι R A)
  (B : Subalgebra R A)
  (b : Module.Basis ι R ↥B)
  -- given
  (hdiscr : Associated (Algebra.discr R (fun i => ((b i : ↥B) : A))) (Algebra.discr R b'))
  (hne : Algebra.discr R b' ≠ 0) :
  -- imply
  B = ⊤ := by
  -- proof
  classical
  let P : Matrix ι ι R := fun i j => b'.repr ((b i : ↥B) : A) j
  have hbP' : (fun i => ((b i : ↥B) : A)) = (P.map (algebraMap R A)).mulVec (b' : ι → A) := by
    funext i
    conv_lhs => rw [← b'.sum_repr ((b i : ↥B) : A)]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def, P]
  have hdisc : Algebra.discr R (fun i => ((b i : ↥B) : A)) = P.det ^ 2 * Algebra.discr R b' := by
    rw [hbP', Algebra.discr_of_matrix_mulVec]
  obtain ⟨u, hu⟩ := hdiscr
  have hunit : IsUnit P.det := by
    have h1 : (P.det ^ 2 * (u : R) - 1) * Algebra.discr R b' = 0 := by
      rw [sub_mul, one_mul, mul_right_comm, ← hdisc, hu, sub_self]
    have h2 : P.det ^ 2 * (u : R) = 1 := sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hne)
    rw [pow_two, mul_assoc] at h2
    apply IsUnit.of_mul_eq_one _ h2
  have hb' : ∀ j, b' j ∈ B := by
    intro j
    have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hunit
    have : (b' : ι → A) = ((P⁻¹).map (algebraMap R A)).mulVec (fun i => ((b i : ↥B) : A)) := by
      rw [hbP', Matrix.mulVec_mulVec, ← Matrix.map_mul, hinv,
        Matrix.map_one (algebraMap R A) (map_zero _) (map_one _), Matrix.one_mulVec]
    have hj := congrFun this j
    rw [hj]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine B.sum_mem fun i _ => ?_
    rw [← Algebra.smul_def]
    apply B.smul_mem (b i).2 _
  rw [eq_top_iff]
  intro a _
  rw [← b'.sum_repr a]
  refine B.sum_mem fun j _ => B.smul_mem (hb' j) _


-- created on 2026-10-20
