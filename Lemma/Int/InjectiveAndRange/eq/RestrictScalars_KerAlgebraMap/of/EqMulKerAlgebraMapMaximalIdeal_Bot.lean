import Mathlib
import sympy.Basic

open IsLocalRing

/--
[IsLocalRing_exists_module_residueField_linearMap_range_eq_ker_of_mul_maximalIdeal_eq_bot](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_exists_module_residueField_linearMap_range_eq_ker_of_mul_maximalIdeal_eq_bot.lean)
-/
@[main]
private lemma main
  {B B₁ : Type} [CommRing B] [IsLocalRing B] [IsArtinianRing B] [CommRing B₁] [Algebra B B₁]
-- given
  (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥) :
-- imply
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ResidueField B) V) (_ : Module.Finite (ResidueField B) V)
      (_ : Module B V) (_ : IsScalarTower B (ResidueField B) V)
      (_ : Module (ResidueField B)ᵐᵒᵖ V) (_ : IsCentralScalar (ResidueField B) V) (ι : V →ₗ[B] B),
      Function.Injective ι ∧ LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)) := by
-- proof
  set J : Ideal B := RingHom.ker (algebraMap B B₁) with hJ
  have htors : Module.IsTorsionBySet B J (maximalIdeal B : Set B) := by
    rintro x ⟨m, hm⟩
    apply Subtype.ext
    show m • (x : B) = 0
    have hmem : (x : B) * m ∈ J * maximalIdeal B := Ideal.mul_mem_mul x.2 hm
    rw [hsmall, Ideal.mem_bot] at hmem
    rw [smul_eq_mul, mul_comm]
    exact hmem
  let modk : Module (ResidueField B) J := htors.module
  have hst : IsScalarTower B (ResidueField B) J := htors.isScalarTower
  have hfin : Module.Finite (ResidueField B) J := Module.Finite.of_restrictScalars_finite B (ResidueField B) J
  let modop : Module (ResidueField B)ᵐᵒᵖ J :=
    Module.compHom J (RingEquiv.toOpposite (ResidueField B)).symm.toRingHom
  have hcs : IsCentralScalar (ResidueField B) J := ⟨fun _ _ => rfl⟩
  refine ⟨J, inferInstance, modk, hfin, inferInstance, hst, modop, hcs, J.subtype, Submodule.injective_subtype J, ?_⟩
  rw [Submodule.range_subtype, Submodule.restrictScalars_self]


-- created on 2026-10-05
