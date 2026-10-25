/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedFreeResolution.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark
-/

import Structure.RingTheory.GradedAlgebra.MultigradedPolynomialModule
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

end MetaMathlibExt
