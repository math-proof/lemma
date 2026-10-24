import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec20GrassmannianCotangent
open Module


/--
[prop37_cotangent_dim_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianCotangent.lean)
-/
@[path]
lemma prop37_cotangent_dim_explicit
  {F : Type u}
  [Field F]
  {W : Type v}
  [AddCommGroup W]
  [Module F W]
  [FiniteDimensional F W]
  {kk : ℕ}
  {V : Module.Grassmannian F W kk} :
-- imply
  Module.finrank F (grassmannianCotangentSpace F W kk V) = kk * (Module.finrank F W - kk) := by
-- proof
  haveI : FiniteDimensional F (W ⧸ V.toSubmodule) := V.finite_quotient
  haveI : FiniteDimensional F V.toSubmodule := Submodule.finiteDimensional_of_le le_top
  haveI : Module.Free F (↥V.toSubmodule) := Module.Free.of_divisionRing F _
  haveI : Module.Free F (W ⧸ V.toSubmodule) := Module.Free.of_divisionRing F _
  change Module.finrank F ((W ⧸ V.toSubmodule) →ₗ[F] ↥V.toSubmodule) = _
  rw [Module.finrank_linearMap F F]
  rw [grassmannian_quotient_finrank F W kk V, grassmannian_submodule_finrank F W kk V]

/--
[prop37_tangent_dim_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianCotangent.lean)
-/
@[path]
lemma prop37_tangent_dim_explicit
  {F : Type u}
  [Field F]
  {W : Type v}
  [AddCommGroup W]
  [Module F W]
  [FiniteDimensional F W]
  {kk : ℕ}
  {V : Module.Grassmannian F W kk} :
-- imply
  Module.finrank F (grassmannianTangentSpace F W kk V) = (Module.finrank F W - kk) * kk := by
-- proof
  haveI : FiniteDimensional F (W ⧸ V.toSubmodule) := V.finite_quotient
  haveI : FiniteDimensional F V.toSubmodule := Submodule.finiteDimensional_of_le le_top
  haveI : Module.Free F (↥V.toSubmodule) := Module.Free.of_divisionRing F _
  haveI : Module.Free F (W ⧸ V.toSubmodule) := Module.Free.of_divisionRing F _
  change Module.finrank F (↥V.toSubmodule →ₗ[F] (W ⧸ V.toSubmodule)) = _
  rw [Module.finrank_linearMap F F]
  rw [grassmannian_quotient_finrank F W kk V, grassmannian_submodule_finrank F W kk V]

/--
[prop37_tangent_cotangent_dim_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianCotangent.lean)
-/
@[path]
lemma prop37_tangent_cotangent_dim_eq
  {F : Type u}
  [Field F]
  {W : Type v}
  [AddCommGroup W]
  [Module F W]
  [FiniteDimensional F W]
  {kk : ℕ}
  {V : Module.Grassmannian F W kk} :
-- imply
  Module.finrank F (grassmannianTangentSpace F W kk V) = Module.finrank F (grassmannianCotangentSpace F W kk V) := by
-- proof
  rw [prop37_tangent_dim_explicit, prop37_cotangent_dim_explicit]
  ring

/--
[prop37_grassmannian_dimension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianCotangent.lean)
-/
@[path]
lemma prop37_grassmannian_dimension
  {F : Type u}
  [Field F]
  {W : Type v}
  [AddCommGroup W]
  [Module F W]
  {n kk : ℕ}
  [FiniteDimensional F W]
  {V : Module.Grassmannian F W kk}
-- given
  (hW : Module.finrank F W = n) :
-- imply
  Module.finrank F (grassmannianCotangentSpace F W kk V) = kk * (n - kk) := by
-- proof
  rw [prop37_cotangent_dim_explicit, hW]

/--
[prop37_projective_cotangent_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianCotangent.lean)
-/
@[path]
lemma prop37_projective_cotangent_dim
  {F : Type u}
  [Field F]
  {W : Type v}
  [AddCommGroup W]
  [Module F W]
  {n : ℕ}
  [FiniteDimensional F W]
  {V : Module.Grassmannian F W 1}
-- given
  (hW : Module.finrank F W = n + 1) :
-- imply
  Module.finrank F (grassmannianCotangentSpace F W 1 V) = n := by
-- proof
  rw [prop37_cotangent_dim_explicit, hW]
  simp


-- created on 2026-10-23
