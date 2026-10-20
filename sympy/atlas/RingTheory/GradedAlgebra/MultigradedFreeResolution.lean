/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedFreeResolution.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark
-/

import sympy.atlas.RingTheory.GradedAlgebra.MultigradedPolynomialModule
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-!
# Multigraded free modules and graded free resolutions

This file provides the multigraded free-module interface over a multivariate
polynomial ring `MvPolynomial (Fin n) K`: degree-preserving maps, free modules
with a homogeneous basis, and graded free resolutions built from Mathlib's
actual projective resolutions with degree-zero differentials and augmentation.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact lines 856–877. Those lines define multigraded free resolutions and
Betti numbers and state that the multigraded Poincaré series of a finitely
generated graded module over a polynomial ring is a polynomial.

Deliberately deferred (not claimed here): tensor base change, component
homology, Betti numbers and their independence, Poincaré series, finite
support, eventual vanishing, and polynomiality. This file only provides the
free graded object, Mathlib's actual projective resolution, and the
degree-zero conditions on successor differentials and the augmentation on
which those later stages will build.

Main definitions:

* `MetaMathlibExt.IsDegreeZero`: a `MvPolynomial (Fin n) K`-linear map sending
  each homogeneous piece of the source grading into the same-degree piece of
  the target grading.
* `MetaMathlibExt.MultigradedFreeModule`: a `ℤⁿ`-graded module equipped with
  an actual `MvPolynomial (Fin n) K`-basis whose basis vectors are homogeneous
  of prescribed degrees.
* `MetaMathlibExt.MultigradedFreeResolution`: Mathlib's actual
  `ProjectiveResolution` of `M`, with each term carrying a
  `MultigradedFreeModule` structure and with degree-zero successor
  differentials and augmentation. The `K`-module structure on resolution terms
  is the local `Module.compHom` instance via `MvPolynomial.C`; no global
  `Module K` instance is installed.
-/

namespace MetaMathlibExt

variable {K : Type*} [Field K] {n : ℕ}

/-- A `MvPolynomial (Fin n) K`-linear map is degree-zero when it sends each
homogeneous piece of the source grading into the same-degree piece of the
target grading. -/
def IsDegreeZero {M N : Type*} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M] [AddCommGroup N]
    [Module (MvPolynomial (Fin n) K) N] [Module K N]
    (gM : MultigradedPolynomialModule K n M)
    (gN : MultigradedPolynomialModule K n N)
    (f : M →ₗ[MvPolynomial (Fin n) K] N) : Prop :=
  ∀ (α : Fin n →₀ Int) (m : M), m ∈ gM.component α → f m ∈ gN.component α

/-- A multigraded free module: a `ℤⁿ`-graded module over
`MvPolynomial (Fin n) K` equipped with an actual basis whose basis vectors
are homogeneous of prescribed degrees. -/
structure MultigradedFreeModule (K : Type*) [Field K] (n : ℕ)
    (F : Type*) [AddCommGroup F] [Module (MvPolynomial (Fin n) K) F]
    [Module K F] (ι : Type*) where
  /-- The underlying `ℤⁿ`-graded module structure. -/
  graded : MultigradedPolynomialModule K n F
  /-- The actual free basis over `MvPolynomial (Fin n) K`. -/
  basis : Module.Basis ι (MvPolynomial (Fin n) K) F
  /-- The prescribed homogeneous degree of each basis vector. -/
  degree : ι → (Fin n →₀ Int)
  /-- Each basis vector is homogeneous of its prescribed degree. -/
  basis_mem : ∀ (i : ι), basis i ∈ graded.component (degree i)

/-- A multigraded free resolution: Mathlib's actual `ProjectiveResolution` of
`M`, with each term carrying a `MultigradedFreeModule` structure and with
degree-zero successor differentials and augmentation. The `K`-module structure
on each resolution term is the local `Module.compHom` instance via
`MvPolynomial.C`; no global `Module K` instance is installed. -/
structure MultigradedFreeResolution (K : Type*) [Field K] (n : ℕ)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : ℕ → Type*) where
  /-- Each resolution term carries a multigraded free module structure. -/
  termFree : ∀ (i : ℕ),
    letI : Module K ↥(resolution.complex.X i) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K);
    MultigradedFreeModule K n ↥(resolution.complex.X i) (ι i)
  /-- Successor differentials are degree-zero. -/
  diffDegreeZero : ∀ (i : ℕ),
    letI : Module K ↥(resolution.complex.X (i + 1)) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K);
    letI : Module K ↥(resolution.complex.X i) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K);
    IsDegreeZero (termFree (i + 1)).graded (termFree i).graded
      (ModuleCat.Hom.hom (resolution.complex.d (i + 1) i))
  /-- The augmentation map is degree-zero. -/
  augDegreeZero :
    letI : Module K ↥(resolution.complex.X 0) :=
      Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K);
    IsDegreeZero (termFree 0).graded targetGraded
      (ModuleCat.Hom.hom (resolution.π.f 0))

end MetaMathlibExt
