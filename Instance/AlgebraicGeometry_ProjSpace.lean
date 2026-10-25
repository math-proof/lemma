-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_ProjSpace.lean: instance decls only.
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Lemma.AlgebraicGeometry.ProjSpace

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry


namespace ProjSpace

section PnSetup

variable (R : Type u) [CommRing R] (n : ℕ)

instance finiteType_mvPolynomial :
    Algebra.FiniteType (𝒜 0) (MvPolynomial (Fin (n + 1)) R) := by
  classical
  refine ⟨⟨Finset.univ.image MvPolynomial.X, eq_top_iff.mpr fun p _ => ?_⟩⟩
  induction p using MvPolynomial.induction_on with
  | C r =>
    exact Subalgebra.algebraMap_mem _ (⟨C r, (mem_homogeneousSubmodule 0 _).mpr
      (isHomogeneous_C _ r)⟩ : 𝒜 0)
  | add p q hp hq => exact Subalgebra.add_mem _ (hp trivial) (hq trivial)
  | mul_X p j hp =>
    exact Subalgebra.mul_mem _ (hp trivial)
      (Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ j))))

instance isProper_π : IsProper (π R n) := by
  unfold π
  haveI : IsProper (Proj.toSpecZero 𝒜) := inferInstance
  haveI : IsIso (CommRingCat.ofHom (grad0Equiv R n).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (grad0Equiv R n).bijective
  haveI : IsIso (Spec.map (CommRingCat.ofHom (grad0Equiv R n).toRingHom)) :=
    inferInstance
  infer_instance

end PnSetup


section Setup

variable (R : Type u) [CommRing R] (n : ℕ)

instance algebraAway (i : Fin (n + 1)) :
    Algebra R (Away 𝒜 (MvPolynomial.X i)) :=
  ((HomogeneousLocalization.fromZeroRingHom 𝒜 _).comp
    (grad0Equiv R n).toRingHom).toAlgebra

end Setup


section ProdOver

variable (R : Type u) [CommRing R]

instance instIsProperProdOverπ {m : ℕ} (e : Fin m → ℕ) : IsProper (prodOverπ R e) :=
  isProper_prodOverπ R e

end ProdOver


end ProjSpace


end AlgebraicGeometry

end
