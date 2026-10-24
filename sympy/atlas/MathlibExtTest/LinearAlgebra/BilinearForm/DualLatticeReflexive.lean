/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/BilinearForm/DualLatticeReflexive.lean -/


import sympy.atlas.LinearAlgebra.BilinearForm.DualLatticeReflexive
import Lemma.Matrix.BilinearForm.DualLatticeReflexive

open LinearMap (BilinForm)

variable {A K V : Type*} [CommRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V]
  [IsScalarTower A K V]

/-- The generic flip double-dual theorem applies with no symmetry hypothesis. -/
example [FiniteDimensional K V] [IsDomain A] (B : BilinForm K V)
    (hB : B.Nondegenerate) (M : Submodule A V) [Submodule.IsLattice K M]
    [Module.IsReflexive A M] :
    B.flip.dualSubmodule (B.dualSubmodule M) = M :=
  B.dualSubmodule_flip_dualSubmodule_of_isLattice hB M

/-- The Dedekind corollary needs no `Module.IsReflexive` hypothesis. -/
example [FiniteDimensional K V] [IsDedekindDomain A] (B : BilinForm K V)
    (hB : B.Nondegenerate) (hBsymm : B.IsSymm) (M : Submodule A V)
    [Submodule.IsLattice K M] :
    B.dualSubmodule (B.dualSubmodule M) = M :=
  B.dualSubmodule_dualSubmodule_of_isLattice hB hBsymm M

/-- Concrete rank-one example: the multiplication form on `ℚ` with lattice `ℤ ∙ 1`. -/
example : LinearMap.BilinForm.dualSubmodule (LinearMap.mul ℚ ℚ)
    (LinearMap.BilinForm.dualSubmodule (LinearMap.mul ℚ ℚ)
      (Submodule.span ℤ {(1 : ℚ)})) =
    Submodule.span ℤ {(1 : ℚ)} := by
  have : Submodule.IsLattice ℚ (Submodule.span ℤ {(1 : ℚ)}) := by
    refine { fg := ?_, span_eq_top := ?_ }
    · exact Submodule.fg_span (Set.finite_singleton (1 : ℚ))
    · rw [eq_top_iff]
      intro x _
      have h1 : (1 : ℚ) ∈ ((Submodule.span ℤ {(1 : ℚ)}) : Set ℚ) :=
        Submodule.subset_span (by simp)
      have hmem : x • (1 : ℚ) ∈
          Submodule.span ℚ ((Submodule.span ℤ {(1 : ℚ)}) : Set ℚ) :=
        Submodule.smul_mem _ x (Submodule.subset_span h1)
      rwa [smul_eq_mul, mul_one] at hmem
  have hBsymm : LinearMap.BilinForm.IsSymm (LinearMap.mul ℚ ℚ : BilinForm ℚ ℚ) :=
    ⟨fun x y => by simp [mul_comm]⟩
  have hB : (LinearMap.mul ℚ ℚ : BilinForm ℚ ℚ).Nondegenerate := by
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · have h := hx 1
      simpa [LinearMap.mul_apply'] using h
    · have h := hy 1
      simpa [LinearMap.mul_apply'] using h
  exact LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_isLattice
    (LinearMap.mul ℚ ℚ) hB hBsymm _
