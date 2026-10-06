import Mathlib
import sympy.Basic

open IsLocalRing

/--
[IsLocalRing_exists_module_residueField_linearMap_range_eq_ker_ringHom_of_mul_maximalIdeal_eq_bot](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_exists_module_residueField_linearMap_range_eq_ker_ringHom_of_mul_maximalIdeal_eq_bot.lean)
-/
@[main]
private lemma main
  {B B₁ : Type u} [CommRing B] [IsLocalRing B] [IsArtinianRing B] [CommRing B₁]
  {π : B →+* B₁}
-- given
  (hsmall : RingHom.ker π * maximalIdeal B = ⊥) :
-- imply
  ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module (ResidueField B) V) (_ : Module.Finite (ResidueField B) V)
      (_ : Module B V) (_ : IsScalarTower B (ResidueField B) V)
      (_ : Module (ResidueField B)ᵐᵒᵖ V) (_ : IsCentralScalar (ResidueField B) V) (ι : V →ₗ[B] B),
      Function.Injective ι ∧ LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker π) := by
-- proof
  classical

  let K : Submodule B B := RingHom.ker π
  have hV : Module.IsTorsionBySet B (↥K) (maximalIdeal B : Set B) := by
    rintro x ⟨m, hm⟩
    apply Subtype.ext
    change m • (x : B) = 0
    have : (x : B) * m ∈ RingHom.ker π * maximalIdeal B := Ideal.mul_mem_mul x.2 hm
    rw [hsmall, Ideal.mem_bot] at this
    rw [smul_eq_mul, mul_comm]; exact this
  have hV' : Module.IsTorsionBySet B (↥K) (↑(maximalIdeal B)) := hV
  letI instK : Module (ResidueField B) ↥K := hV'.module
  haveI instT : IsScalarTower B (ResidueField B) ↥K := hV'.isScalarTower
  haveI : Module.Finite B ↥K := Module.Finite.of_fg (IsNoetherian.noetherian K)
  haveI instF : Module.Finite (ResidueField B) ↥K :=
    Module.Finite.of_restrictScalars_finite B (ResidueField B) ↥K
  letI instM : Module (ResidueField B)ᵐᵒᵖ ↥K :=
    Module.compHom ↥K ((RingEquiv.toOpposite (ResidueField B)).symm : (ResidueField B)ᵐᵒᵖ →+* ResidueField B)
  haveI instC : IsCentralScalar (ResidueField B) ↥K := ⟨fun r x => rfl⟩
  refine ⟨↥K, inferInstance, instK, instF, inferInstance, instT, instM, instC, K.subtype,
    Subtype.val_injective, ?_⟩
  rw [Submodule.range_subtype, Submodule.restrictScalars_self]


-- created on 2026-10-05
