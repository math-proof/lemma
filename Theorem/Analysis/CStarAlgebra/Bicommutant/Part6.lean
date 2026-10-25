import Mathlib.Analysis.InnerProductSpace.Adjoint
import Def.Analysis.CStarAlgebra.Bicommutant.Part6


namespace Complex.CStarAlgebra.Bicommutant

open Matrix ComplexInnerProductSpace

/-- The cyclic subspace is invariant under the amplified action. -/
theorem cycSub_invariant (n : ℕ)
    (S : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (C : Matrix (Fin n) (Fin n) ℂ) (hC : C ∈ (S : Set _)) :
    ∀ y ∈ cycSub n S, ampOp n n C y ∈ cycSub n S := by
  have hgen : ∀ y ∈ Set.range
      (fun s : ↥S => ampOp n n (s : Matrix (Fin n) (Fin n) ℂ) (cycVec n)),
      ampOp n n C y ∈ cycSub n S := by
    rintro y ⟨s, rfl⟩
    have hmem : C * (s : Matrix (Fin n) (Fin n) ℂ) ∈ (S : Set _) :=
      mul_mem hC s.prop
    have hmul : ampOp n n C (ampOp n n (s : Matrix (Fin n) (Fin n) ℂ) (cycVec n)) =
        ampOp n n (C * s) (cycVec n) := by
      rw [ampOp_mul, LinearMap.comp_apply]
    rw [hmul]
    exact Submodule.subset_span ⟨⟨C * s, hmem⟩, rfl⟩
  have hle : cycSub n S ≤ Submodule.comap (ampOp n n C) (cycSub n S) :=
    Submodule.span_le.mpr hgen
  intro y hy
  exact hle hy

/-- Finite-dimensional von Neumann bicommutant theorem for matrices.

This is the finite-dimensional specialization of John von Neumann, "Zur Algebra der
Funktionaloperationen und Theorie der normalen Operatoren", Mathematische Annalen 102
(1930), 370--427, DOI 10.1007/BF01782352. In finite dimension every subspace is closed,
so the strong-operator closure condition of the general theorem is vacuous and the
double commutant of a unital `∗`-subalgebra equals the algebra itself. -/
theorem bicommutant_finiteDimensional_matrix (n : ℕ)
    (S : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    StarSubalgebra.centralizer ℂ
        ((StarSubalgebra.centralizer ℂ (S : Set (Matrix (Fin n) (Fin n) ℂ)) :
          Set (Matrix (Fin n) (Fin n) ℂ))) = S := by
  apply le_antisymm
  · intro B hB
    have hPcomm : ∀ A ∈ (S : Set (Matrix (Fin n) (Fin n) ℂ)),
        (cycSub n S).starProjection.toLinearMap.comp (ampOp n n A) =
          (ampOp n n A).comp (cycSub n S).starProjection.toLinearMap :=
      fun A hA => proj_comm_of_invariant n n _ _
        (fun A hA v hv => cycSub_invariant n S A hA v hv)
        (fun A hA v hv =>
          cycSub_invariant n S (star A) (StarMemClass.star_mem hA) v hv)
        A hA
    have hPB : (ampOp n n B).comp (cycSub n S).starProjection.toLinearMap =
        (cycSub n S).starProjection.toLinearMap.comp (ampOp n n B) :=
      amp_comm_of_mem n n S B hB _ hPcomm
    have hξK : cycVec n ∈ cycSub n S := by
      have h1 : ampOp n n 1 (cycVec n) = cycVec n := by
        rw [ampOp_one, LinearMap.id_apply]
      exact Submodule.subset_span ⟨⟨1, one_mem S⟩, h1⟩
    have hPξ : (cycSub n S).starProjection.toLinearMap (cycVec n) = cycVec n := by
      change (cycSub n S).starProjection (cycVec n) = cycVec n
      exact Submodule.starProjection_eq_self_iff.mpr hξK
    have hBξ : ampOp n n B (cycVec n) ∈ cycSub n S := by
      have hPBξ := LinearMap.congr_fun hPB (cycVec n)
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hPξ] at hPBξ
      rw [hPBξ]
      change (cycSub n S).starProjection (ampOp n n B (cycVec n)) ∈ cycSub n S
      exact Submodule.starProjection_apply_mem _ _
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hBξ
    have hc' : (∑ s ∈ c.support,
        (c s) • ampOp n n (s : Matrix (Fin n) (Fin n) ℂ) (cycVec n)) =
        ampOp n n B (cycVec n) := hc
    set A₀ : Matrix (Fin n) (Fin n) ℂ :=
      ∑ s ∈ c.support, (c s) • (s : Matrix (Fin n) (Fin n) ℂ) with hA₀def
    have hA₀ : A₀ ∈ S := by
      apply sum_mem
      intro s _
      exact StarSubalgebra.smul_mem S s.prop (c s)
    have hcomp : ∀ j : Fin n, B *ᵥ Pi.single (M := fun _ : Fin n => ℂ) j 1 =
        A₀ *ᵥ Pi.single (M := fun _ : Fin n => ℂ) j 1 := by
      intro j
      have h3 : ∀ M : Matrix (Fin n) (Fin n) ℂ,
          matToOp n M (WithLp.toLp 2 (Pi.single (M := fun _ : Fin n => ℂ) j 1)) =
            WithLp.toLp 2
              (M *ᵥ Pi.single (M := fun _ : Fin n => ℂ) j 1) := by
        intro M
        change Matrix.toEuclideanLin M _ = _
        exact Matrix.toLpLin_apply 2 2 M _
      have h1j := congrArg (fun w => w.ofLp j) hc'
      rw [WithLp.ofLp_sum, Finset.sum_apply] at h1j
      simp only [WithLp.ofLp_smul, Pi.smul_apply, ampOp_apply, cycVec_ofLp, h3,
        ← WithLp.toLp_sum] at h1j
      -- h1j : toLp (∑ s ∈ support, (c s) • (s *ᵥ single)) = toLp (B *ᵥ single)
      have h5 := congrArg WithLp.ofLp h1j
      have h4 : A₀ *ᵥ Pi.single (M := fun _ : Fin n => ℂ) j 1 =
          ∑ s ∈ c.support, (c s) • ((s : Matrix (Fin n) (Fin n) ℂ) *ᵥ
            Pi.single (M := fun _ : Fin n => ℂ) j 1) := by
        rw [hA₀def, Matrix.sum_mulVec]
        apply Finset.sum_congr rfl
        intro s _
        exact Matrix.smul_mulVec _ _ _
      rw [h4]
      exact h5.symm
    have hBA : B = A₀ := Matrix.ext_of_mulVec_single hcomp
    rw [hBA]
    exact hA₀
  · intro B hB
    have h := StarAlgebra.adjoin_le_centralizer_centralizer ℂ
      (S : Set (Matrix (Fin n) (Fin n) ℂ))
    rw [StarAlgebra.adjoin_eq] at h
    exact h hB

end Complex.CStarAlgebra.Bicommutant
