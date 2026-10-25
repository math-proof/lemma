import Mathlib
import sympy.Basic
import Theorem.NumberTheory.NumberField.RayClass.QuotientToRayClass.Part3
open scoped nonZeroDivisors
open NumberField
open Modulus


namespace NumberField.Modulus

/--
[principalRayIdealMap_integralUnitsToRayElements](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
lemma principalRayIdealMap_integralUnitsToRayElements
  [Field K] [NumberField K]
  {m : Modulus K}
  {u : (𝓞 K)ˣ} :
-- imply
  principalRayIdealMap m (integralUnitsToRayElements m u) = 1 := by
-- proof
  apply Subtype.ext
  rw [principalRayIdealMap_apply]
  have h : toPrincipalIdeal (𝓞 K) K
    ((integralUnitsToRayElements m u : rayElements m) : Kˣ) =
    toPrincipalIdeal (𝓞 K) K 1 := by
    rw [toPrincipalIdeal_eq_iff_exists_integralUnit_mul]
    exact ⟨u, by simp [integralUnitsToRayElements_coe,
      integralUnitsToFieldUnits]⟩
  simpa using h

end NumberField.Modulus

namespace NumberField.Modulus

/--
[rayQuotientToRayClassGroup_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
lemma rayQuotientToRayClassGroup_ker
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (rayQuotientToRayClassGroup m).ker =
    MonoidHom.range (integralUnitsToRayQuotient m) := by
-- proof
  apply le_antisymm
  · intro q hq
    rw [MonoidHom.mem_ker] at hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (rayOneElements m) q
    rw [QuotientGroup.mk'_apply, rayQuotientToRayClassGroup_mk,
      rayElementClassMap_apply, rayClassMap_eq_one_iff] at hq
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp
      ((rayGroup_eq_map_rayOneElements m).symm ▸ hq)
    have htop : toPrincipalIdeal (𝓞 K) K (x : Kˣ) =
      toPrincipalIdeal (𝓞 K) K (y : Kˣ) := by
      have hcongr := congrArg Subtype.val hxy
      have hx : ((principalRayIdealMap m x : coprimeFractionalIdeals m) :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
        toPrincipalIdeal (𝓞 K) K (x : Kˣ) :=
        principalRayIdealMap_apply m x
      have hy' : ((principalRayIdealMap m y : coprimeFractionalIdeals m) :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
        toPrincipalIdeal (𝓞 K) K (y : Kˣ) :=
        principalRayIdealMap_apply m y
      rwa [hx, hy'] at hcongr
    obtain ⟨u, hu⟩ :=
      (toPrincipalIdeal_eq_iff_exists_integralUnit_mul (x : Kˣ) (y : Kˣ)).mp htop
    refine MonoidHom.mem_range.mpr ⟨u, ?_⟩
    rw [integralUnitsToRayQuotient_apply]
    symm
    change (x : rayElements m ⧸ rayOneElements m) =
      ((integralUnitsToRayElements m u : rayElements m) :
        rayElements m ⧸ rayOneElements m)
    rw [QuotientGroup.eq_iff_div_mem]
    have hdiv : x / integralUnitsToRayElements m u = y := by
      apply Subtype.ext
      simp only [Subgroup.coe_div, integralUnitsToRayElements_coe,
        integralUnitsToFieldUnits, RingHom.toMonoidHom_eq_coe]
      change (x : Kˣ) / Units.map (algebraMap (𝓞 K) K) u = (y : Kˣ)
      rw [hu, mul_comm]
      exact mul_div_cancel_right _ _
    rwa [hdiv]
  · intro q hq
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hq
    rw [MonoidHom.mem_ker, integralUnitsToRayQuotient_apply,
      rayQuotientToRayClassGroup_mk, rayElementClassMap_apply]
    rw [principalRayIdealMap_integralUnitsToRayElements, map_one]

end NumberField.Modulus

namespace NumberField.Modulus

/--
[integralUnitsToRayQuotient_mulExact_rayQuotientToRayClassGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
lemma integralUnitsToRayQuotient_mulExact_rayQuotientToRayClassGroup
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.MulExact (integralUnitsToRayQuotient m)
    (rayQuotientToRayClassGroup m) := by
-- proof
  rw [MonoidHom.mulExact_iff, rayQuotientToRayClassGroup_ker]

end NumberField.Modulus

namespace NumberField.Modulus

/--
[residueSignToRayClassGroup_residueSignMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
lemma residueSignToRayClassGroup_residueSignMap
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  residueSignToRayClassGroup m (residueSignMap m x) =
    rayElementClassMap m x := by
-- proof
  calc residueSignToRayClassGroup m (residueSignMap m x)
    = residueSignToRayClassGroup m
      (rayElementsQuotientEquivResidueSign m (QuotientGroup.mk x)) := by
      rw [rayElementsQuotientEquivResidueSign_mk]
    _ = rayQuotientToRayClassGroup m (QuotientGroup.mk x) :=
      residueSignToRayClassGroup_equiv m _
    _ = rayElementClassMap m x := rayQuotientToRayClassGroup_mk m x

end NumberField.Modulus

namespace NumberField.Modulus

/--
[residueSignToRayClassGroup_comp_residueSignMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
lemma residueSignToRayClassGroup_comp_residueSignMap
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (residueSignToRayClassGroup m).comp (residueSignMap m) =
    rayElementClassMap m := by
-- proof
  ext x
  simp only [MonoidHom.comp_apply]
  exact residueSignToRayClassGroup_residueSignMap m x

end NumberField.Modulus

namespace NumberField.Modulus

/--
[residueSignToRayClassGroup_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
lemma residueSignToRayClassGroup_ker
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (residueSignToRayClassGroup m).ker =
    MonoidHom.range (integralUnitsToResidueSign m) := by
-- proof
  unfold residueSignToRayClassGroup integralUnitsToResidueSign
  change
    ((rayQuotientToRayClassGroup m).comp
      (rayElementsQuotientEquivResidueSign m).symm).ker =
    ((rayElementsQuotientEquivResidueSign m).toMonoidHom.comp
      (integralUnitsToRayQuotient m)).range
  rw [MonoidHom.ker_comp_mulEquiv, MonoidHom.range_comp,
    rayQuotientToRayClassGroup_ker, MulEquiv.symm_symm,
    MulEquiv.toMonoidHom_eq_coe]

end NumberField.Modulus

namespace NumberField.Modulus

/--
[integralUnitsToResidueSign_mulExact_residueSignToRayClassGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
lemma integralUnitsToResidueSign_mulExact_residueSignToRayClassGroup
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.MulExact (integralUnitsToResidueSign m)
    (residueSignToRayClassGroup m) := by
-- proof
  rw [MonoidHom.mulExact_iff, residueSignToRayClassGroup_ker]

end NumberField.Modulus

/--
[rayElementClassMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
private lemma rayElementClassMap_apply_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  rayElementClassMap m x = rayClassMap m (principalRayIdealMap m x) := by
-- proof
  apply NumberField.Modulus.rayElementClassMap_apply m x

/--
[rayOneElements_le_rayElementClassMap_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
private lemma rayOneElements_le_rayElementClassMap_ker_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  rayOneElements m ≤ (rayElementClassMap m).ker := by
-- proof
  apply NumberField.Modulus.rayOneElements_le_rayElementClassMap_ker m

/--
[rayQuotientToRayClassGroup_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
private lemma rayQuotientToRayClassGroup_mk_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  rayQuotientToRayClassGroup m (QuotientGroup.mk x) =
    rayElementClassMap m x := by
-- proof
  apply NumberField.Modulus.rayQuotientToRayClassGroup_mk m x

/--
[residueSignToRayClassGroup_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean)
-/
@[path]
private lemma residueSignToRayClassGroup_equiv_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {q : rayElements m ⧸ rayOneElements m} :
-- imply
  residueSignToRayClassGroup m (rayElementsQuotientEquivResidueSign m q) =
    rayQuotientToRayClassGroup m q := by
-- proof
  apply NumberField.Modulus.residueSignToRayClassGroup_equiv m q


-- created on 2026-10-20
-- updated on 2026-10-23
