import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.SymplecticStandardBasis
open Module FiniteDimensional SymplecticLinearAlgebra


/--
[exists_symplectic_pair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticStandardBasis.lean)
-/
@[path]
private lemma exists_symplectic_pair_eq
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {Ω : LinearMap.BilinForm ℝ V}
-- given
  (hΩ : IsSymplecticForm Ω)
  (hne : Nontrivial V) :
-- imply
  ∃ (e₁ f₁ : V), Ω e₁ f₁ = 1 ∧ IsSymplecticSubspace Ω (Submodule.span ℝ {e₁, f₁}) := by
-- proof
  apply SymplecticLinearAlgebra.exists_symplectic_pair hΩ hne

/--
[restrict_symplecticOrtho_symplectic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticStandardBasis.lean)
-/
@[path]
private lemma restrict_symplecticOrtho_symplectic_eq
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {Ω : LinearMap.BilinForm ℝ V}
  {P : Submodule ℝ V}
-- given
  (hΩ : IsSymplecticForm Ω)
  (hCompl : IsCompl P (symplecticOrtho Ω P)) :
-- imply
  IsSymplecticForm (Ω.restrict (symplecticOrtho Ω P)) := by
-- proof
  apply SymplecticLinearAlgebra.restrict_symplecticOrtho_symplectic hΩ hCompl

/--
[ortho_of_mem_symplecticOrtho](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticStandardBasis.lean)
-/
@[path]
private lemma ortho_of_mem_symplecticOrtho_eq
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {Ω : LinearMap.BilinForm ℝ V}
  {P : Submodule ℝ V}
  {u : V}
  {p : V}
-- given
  (hΩ : IsSymplecticForm Ω)
  (hu : u ∈ symplecticOrtho Ω P)
  (hp : p ∈ P) :
-- imply
  Ω u p = 0 := by
-- proof
  apply SymplecticLinearAlgebra.ortho_of_mem_symplecticOrtho hΩ hu hp

/--
[symplectic_standard_basis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticStandardBasis.lean)
-/
@[path]
private lemma symplectic_standard_basis_eq
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {Ω : LinearMap.BilinForm ℝ V}
-- given
  (hΩ : IsSymplecticForm Ω) :
-- imply
  ∃ n : ℕ, ∃ e f : Fin n → V, finrank ℝ V = 2 * n ∧ (∀ i j, Ω (e i) (e j) = 0) ∧ (∀ i j, Ω (f i) (f j) = 0) ∧ (∀ i j, Ω (e i) (f j) = if i = j then 1 else 0) ∧ LinearIndependent ℝ (Sum.elim e f) ∧ ⊤ ≤ Submodule.span ℝ (Set.range (Sum.elim e f)) := by
-- proof
  apply SymplecticLinearAlgebra.symplectic_standard_basis hΩ


-- created on 2026-10-23
