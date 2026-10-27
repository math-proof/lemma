import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.NumberTheory.NumberField.RayClass.PrincipalIdeal
open scoped nonZeroDivisors
open NumberField
open Modulus


namespace NumberField.Modulus

/--
[toPrincipalIdeal_eq_iff_exists_integralUnit_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/PrincipalIdeal.lean)
-/
@[path]
lemma toPrincipalIdeal_eq_iff_exists_integralUnit_mul
  [Field K] [NumberField K]
  {x y : Kˣ} :
-- imply
  toPrincipalIdeal (𝓞 K) K x = toPrincipalIdeal (𝓞 K) K y ↔
    ∃ u : (𝓞 K)ˣ,
    x = Units.map (algebraMap (𝓞 K) K).toMonoidHom u * y := by
-- proof
  constructor
  · intro h
    have hcoe : FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (y : K) := by
      have := congrArg (fun u : (FractionalIdeal (𝓞 K)⁰ K)ˣ =>
        (u : FractionalIdeal (𝓞 K)⁰ K)) h
      rwa [coe_toPrincipalIdeal, coe_toPrincipalIdeal] at this
    rw [FractionalIdeal.spanSingleton_eq_spanSingleton] at hcoe
    obtain ⟨z, hz⟩ := hcoe
    refine ⟨z⁻¹, ?_⟩
    rw [Units.smul_def, Algebra.smul_def] at hz
    have hU : Units.map (algebraMap (𝓞 K) K).toMonoidHom z * x = y := by
      apply Units.ext
      simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe,
        MonoidHom.coe_coe]
      exact hz
    rw [map_inv, ← hU, inv_mul_cancel_left]
  · rintro ⟨u, rfl⟩
    rw [map_mul]
    have hunit : toPrincipalIdeal (𝓞 K) K
      (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) = 1 := by
      apply Units.ext
      rw [Units.val_one, coe_toPrincipalIdeal]
      have hmem : FractionalIdeal.spanSingleton (𝓞 K)⁰
        (Units.map (algebraMap (𝓞 K) K).toMonoidHom u : Kˣ).val =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K) := by
        rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
        refine ⟨u⁻¹, ?_⟩
        rw [Units.smul_def, Algebra.smul_def, Units.coe_map,
          RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
        rw [← map_mul, Units.inv_mul, map_one]
      rwa [FractionalIdeal.spanSingleton_one] at hmem
    rw [hunit, one_mul]

end NumberField.Modulus

/--
[principalRayIdealMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/PrincipalIdeal.lean)
-/
@[path]
private lemma principalRayIdealMap_apply_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  (principalRayIdealMap m x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
    toPrincipalIdeal (𝓞 K) K (x : Kˣ) := by
-- proof
  apply NumberField.Modulus.principalRayIdealMap_apply m x

/--
[rayGroup_eq_map_rayOneElements](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/PrincipalIdeal.lean)
-/
@[path]
private lemma rayGroup_eq_map_rayOneElements_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  rayGroup m = (rayOneElements m).map (principalRayIdealMap m) := by
-- proof
  apply NumberField.Modulus.rayGroup_eq_map_rayOneElements m


-- created on 2026-10-20
-- updated on 2026-10-26
