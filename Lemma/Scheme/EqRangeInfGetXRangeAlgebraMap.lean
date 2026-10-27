import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_IsAffineOpen_range_algebraMap_functionField_eq_iInf](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsAffineOpen_range_algebraMap_functionField_eq_iInf.lean)
-/
@[path]
private lemma main
  {X : Scheme} [IsIntegral X]
  {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
  (algebraMap (X.presheaf.obj (Opposite.op U)) X.functionField).range =
    ⨅ (x : X) (_ : x ∈ U), (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  set A := X.presheaf.obj (Opposite.op U) with hA
  set F := X.functionField with hF
  let _ : IsFractionRing A F := functionField_isFractionRing_of_isAffineOpen X U hU
  apply le_antisymm
  ·
    refine le_iInf₂ fun x hx => ?_
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
    let _ : IsScalarTower A (X.presheaf.stalk x) F := functionField_isScalarTower X U ⟨x, hx⟩
    rintro _ ⟨a, rfl⟩
    exact ⟨algebraMap A (X.presheaf.stalk x) a, (IsScalarTower.algebraMap_apply A _ F a).symm⟩
  ·
    intro f hf
    have key : f ∈ (⨅ v : PrimeSpectrum A,
        Localization.subalgebra.ofField F _ v.asIdeal.primeCompl_le_nonZeroDivisors) := by
      refine Algebra.mem_iInf.mpr fun v => ?_
      have hxU : (hU.fromSpec v : X) ∈ U := by
        show (hU.fromSpec v : X) ∈ (U : Set X)
        rw [← hU.range_fromSpec]
        exact ⟨v, rfl⟩
      let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hU.fromSpec v, hxU⟩ : U)
      let _ : IsScalarTower A (X.presheaf.stalk (hU.fromSpec v : X)) F :=
        functionField_isScalarTower X U ⟨_, hxU⟩
      let _ : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec v : X)) v.asIdeal :=
        hU.isLocalization_stalk' v hxU
      have hfx : f ∈ (algebraMap (X.presheaf.stalk (hU.fromSpec v : X)) F).range :=
        (Subring.mem_iInf.mp ((Subring.mem_iInf.mp hf) (hU.fromSpec v : X))) hxU
      obtain ⟨s, rfl⟩ := hfx
      obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl s
      refine ⟨a, t, t.2, ?_⟩
      have ht : algebraMap A F t ≠ 0 := by
        intro h0
        have : (t : A) = 0 := (IsFractionRing.injective A F) (by rw [h0, map_zero])
        refine t.2 ?_
        rw [this]
        refine v.asIdeal.zero_mem
      rw [eq_mul_inv_iff_mul_eq₀ ht,
        IsScalarTower.algebraMap_apply A (X.presheaf.stalk (hU.fromSpec v : X)) F (t : A),
        ← map_mul, IsLocalization.mk'_spec,
        ← IsScalarTower.algebraMap_apply A (X.presheaf.stalk (hU.fromSpec v : X)) F a]
    rw [PrimeSpectrum.iInf_localization_eq_bot, Algebra.mem_bot] at key
    obtain ⟨a, rfl⟩ := key
    exact ⟨a, rfl⟩


-- created on 2026-10-20
