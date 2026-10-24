/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/BilinearForm/Prod.lean -/


import sympy.atlas.LinearAlgebra.BilinearForm.Prod
import Lemma.Matrix.BilinearForm.Prod
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Tests for the orthogonal product of bilinear forms

Examples exercising `BilinForm.prod` and its nondegeneracy, perfectness,
and dual-submodule API, including a source-shaped Noetherian-domain
fraction-field case.
-/

open LinearMap (BilinForm)
open Module

namespace LinearMap
namespace BilinForm

section Formula

variable {R M₁ M₂ : Type*} [CommSemiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]

-- The evaluation formula fires as a simp lemma.
example (B₁ : BilinForm R M₁) (B₂ : BilinForm R M₂) (x y : M₁ × M₂) :
    B₁.prod B₂ x y = B₁ x.1 y.1 + B₂ x.2 y.2 := by
  simp

-- Forward direction of the nondegeneracy characterisation.
example {B₁ : BilinForm R M₁} {B₂ : BilinForm R M₂}
    (h : (B₁.prod B₂).Nondegenerate) :
    B₁.Nondegenerate ∧ B₂.Nondegenerate :=
  nondegenerate_prod_iff.mp h

-- Reverse direction of the nondegeneracy characterisation.
example {B₁ : BilinForm R M₁} {B₂ : BilinForm R M₂}
    (h₁ : B₁.Nondegenerate) (h₂ : B₂.Nondegenerate) :
    (B₁.prod B₂).Nondegenerate :=
  nondegenerate_prod_iff.mpr ⟨h₁, h₂⟩

end Formula

section TrivialFactor

-- A product with a trivial factor is nondegenerate when the other
-- factor is: both separating conditions hold vacuously on `Fin 0 → ℚ`.
example (B₁ : BilinForm ℚ ℚ) (h₁ : B₁.Nondegenerate)
    (B₂ : BilinForm ℚ (Fin 0 → ℚ)) :
    (B₁.prod B₂).Nondegenerate := by
  rw [nondegenerate_prod_iff]
  refine ⟨h₁, ⟨fun x _ => Subsingleton.elim x 0, fun y _ => ?_⟩⟩
  exact Subsingleton.elim y 0

end TrivialFactor

section PerfPair

/-- A concrete perfect pairing from the canonical dual equivalence. -/
noncomputable abbrev testPair : BilinForm ℚ (Fin 1 → ℚ) :=
  (Module.Free.chooseBasis ℚ (Fin 1 → ℚ)).toDualEquiv.toLinearMap

-- The definitional pairing is perfect via the linear-equivalence route.
example : testPair.IsPerfPair := inferInstance

-- The orthogonal product of perfect pairings is perfect, found by
-- typeclass resolution through `BilinForm.instIsPerfPairProd`.
example : (testPair.prod testPair).IsPerfPair := inferInstance

end PerfPair

section DualSubmodule

variable {R S M₁ M₂ : Type*} [CommRing R] [Field S]
  [AddCommGroup M₁] [AddCommGroup M₂] [Algebra R S]
  [Module R M₁] [Module R M₂] [Module S M₁] [Module S M₂]
  [IsScalarTower R S M₁] [IsScalarTower R S M₂]

-- Dual submodules commute with orthogonal products, with no lattice,
-- Noetherian, domain, or nondegeneracy hypotheses.
example (B₁ : BilinForm S M₁) (B₂ : BilinForm S M₂)
    (N₁ : Submodule R M₁) (N₂ : Submodule R M₂) :
    (B₁.prod B₂).dualSubmodule (N₁.prod N₂) =
      (B₁.dualSubmodule N₁).prod (B₂.dualSubmodule N₂) :=
  dualSubmodule_prod _ _ _ _

end DualSubmodule

section SourceShaped

variable {R K M₁ M₂ : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [Field K] [Algebra R K]
  [AddCommGroup M₁] [AddCommGroup M₂]
  [Module R M₁] [Module R M₂] [Module K M₁] [Module K M₂]
  [IsScalarTower R K M₁] [IsScalarTower R K M₂]

-- Source-shaped case: over a Noetherian domain with fraction field,
-- the product of perfect pairings is perfect and duals split.
-- `IsFractionRing` is deliberately carried as an unused hypothesis to
-- mirror the source context; neither conclusion needs it.
example (B₁ : BilinForm K M₁) (B₂ : BilinForm K M₂)
    [B₁.IsPerfPair] [B₂.IsPerfPair]
    (N₁ : Submodule R M₁) (N₂ : Submodule R M₂)
    (_hFrac : IsFractionRing R K) :
    (B₁.prod B₂).IsPerfPair ∧
      (B₁.prod B₂).dualSubmodule (N₁.prod N₂) =
        (B₁.dualSubmodule N₁).prod (B₂.dualSubmodule N₂) :=
  ⟨inferInstance, dualSubmodule_prod _ _ _ _⟩

end SourceShaped

end BilinForm
end LinearMap
