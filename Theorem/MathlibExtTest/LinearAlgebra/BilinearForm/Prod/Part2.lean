/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/BilinearForm/Prod.lean -/


import Instance.LinearAlgebra.BilinearForm.Prod
import Lemma.Matrix.BilinearForm.Prod
import Mathlib.RingTheory.Localization.FractionRing
import Abbrev.MathlibExtTest.LinearAlgebra.BilinearForm.Prod
open LinearMap (BilinForm)
open Module

/-!
# Tests for the orthogonal product of bilinear forms

Examples exercising `BilinForm.prod` and its nondegeneracy, perfectness,
and dual-submodule API, including a source-shaped Noetherian-domain
fraction-field case.
-/


namespace LinearMap

namespace BilinForm

section PerfPair

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
