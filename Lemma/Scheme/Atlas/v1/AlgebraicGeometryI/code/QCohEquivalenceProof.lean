import Mathlib
import sympy.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.QCohEquivalenceProof
open QCohEquivalenceProof
open Submodule
open CategoryTheory AlgebraicGeometry


namespace QCohEquivalenceProof

/--
[adjunction_equivalence_from_stalks](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohEquivalenceProof.lean)
-/
@[path]
lemma adjunction_equivalence_from_stalks
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup N]
  [Module R N]
  {η : M →ₗ[R] N}
  {ε : N →ₗ[R] M}
-- given
  (h_comp_unit : ∀ (P : Ideal R) [P.IsMaximal], LocalizedModule.map P.primeCompl (ε ∘ₗ η) = LinearMap.id)
  (h_comp_counit : ∀ (P : Ideal R) [P.IsMaximal], LocalizedModule.map P.primeCompl (η ∘ₗ ε) = LinearMap.id) :
-- imply
  ε ∘ₗ η = LinearMap.id ∧ η ∘ₗ ε = LinearMap.id := by
-- proof
  constructor
  · ext m
    simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq]
    refine @Module.eq_of_localization_maximal R M _ _ _
      (fun P _ => LocalizedModule P.primeCompl M)
      (fun P _ => inferInstance) (fun P _ => inferInstance)
      (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M)
      (fun P _ => inferInstance)
      (ε (η m)) m (fun P _ => ?_)
    have h1 := congr_fun (congr_arg DFunLike.coe (h_comp_unit P))
      (LocalizedModule.mkLinearMap P.primeCompl M m)
    simp only [LinearMap.id_coe, id_eq] at h1
    rw [show (LocalizedModule.map P.primeCompl (ε ∘ₗ η))
      (LocalizedModule.mkLinearMap P.primeCompl M m) =
      LocalizedModule.mkLinearMap P.primeCompl M ((ε ∘ₗ η) m) from
      IsLocalizedModule.map_apply P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl M)
        (LocalizedModule.mkLinearMap P.primeCompl M) (ε ∘ₗ η) m] at h1
    exact h1
  · ext n
    simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq]
    refine @Module.eq_of_localization_maximal R N _ _ _
      (fun P _ => LocalizedModule P.primeCompl N)
      (fun P _ => inferInstance) (fun P _ => inferInstance)
      (fun P _ => LocalizedModule.mkLinearMap P.primeCompl N)
      (fun P _ => inferInstance)
      (η (ε n)) n (fun P _ => ?_)
    have h1 := congr_fun (congr_arg DFunLike.coe (h_comp_counit P))
      (LocalizedModule.mkLinearMap P.primeCompl N n)
    simp only [LinearMap.id_coe, id_eq] at h1
    rw [show (LocalizedModule.map P.primeCompl (η ∘ₗ ε))
      (LocalizedModule.mkLinearMap P.primeCompl N n) =
      LocalizedModule.mkLinearMap P.primeCompl N ((η ∘ₗ ε) n) from
      IsLocalizedModule.map_apply P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl N)
        (LocalizedModule.mkLinearMap P.primeCompl N) (η ∘ₗ ε) n] at h1
    exact h1

end QCohEquivalenceProof


-- created on 2026-10-23
