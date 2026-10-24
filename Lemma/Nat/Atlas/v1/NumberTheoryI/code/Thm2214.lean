import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Thm2214
open GlobalCFT RayClassField
open scoped NumberField


namespace RayClassField

/--
[approx_theorem_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm2214.lean)
-/
@[path]
lemma approx_theorem_local
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪 𝔫 : Modulus K}
  {x : FracIdealsCoprime K 𝔪}
-- given
  (h : Modulus.dvd 𝔪 𝔫) :
-- imply
  ∃ (y : FracIdealsCoprime K 𝔫) (r : FracIdealsCoprime K 𝔪), r ∈ RayGroup K 𝔪 ∧ x = (FracIdealsCoprime.inclusion K 𝔪 𝔫 h) y * r :=
-- proof
FracIdealsCoprime.approx_theorem K 𝔪 𝔫 h x

end RayClassField

namespace RayClassField

/--
[RayClassGroup.mapOfDvd_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm2214.lean)
-/
@[path]
lemma RayClassGroup.mapOfDvd_surjective
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔪₁ 𝔪₂ : Modulus K}
-- given
  (h : 𝔪₁.dvd 𝔪₂) :
-- imply
  Function.Surjective (RayClassGroup.mapOfDvd h) := by
-- proof
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (RayGroup K 𝔪₁) q
  obtain ⟨z, r, hr, hyr⟩ := approx_theorem_local 𝔪₁ 𝔪₂ h y
  refine ⟨QuotientGroup.mk' _ z, ?_⟩
  simp only [RayClassGroup.mapOfDvd]
  erw [QuotientGroup.map_mk']
  erw [QuotientGroup.eq]
  rw [hyr]
  simp only [inv_mul_cancel_left]
  exact hr

end RayClassField

namespace RayClassField

/--
[isEquiv_kernel_of_induced](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm2214.lean)
-/
@[path]
lemma isEquiv_kernel_of_induced
  {K : Type u}
  [Field K]
  [NumberField K]
  {m m' : Modulus K}
  {chi : RayClassChar K m}
  {chi' : RayClassChar K m'}
-- given
  (h : m'.dvd m)
  (hind : IsInducedBy K m' m h chi' chi) :
-- imply
  chi.kernelCongruenceSubgroup.IsEquiv chi'.kernelCongruenceSubgroup := by
-- proof
  have hmapOfDvd_eq : ∀ (x : FracIdealsCoprime K m),
    RayClassGroup.mapOfDvd h (toRayClass K m x) =
      toRayClass K m' (FracIdealsCoprime.inclusion K m' m h x) := by
    intro x
    show QuotientGroup.map _ _ _ _ ((QuotientGroup.mk' _) x) = (QuotientGroup.mk' _) _
    rw [QuotientGroup.map_mk']; rfl
  have hincl_subtype : ∀ (x : FracIdealsCoprime K m),
    ((FracIdealsCoprime_subgroup K m').subtype
      (FracIdealsCoprime.inclusion K m' m h x) : (FracIdeal K)ˣ) =
    (FracIdealsCoprime_subgroup K m).subtype x := by
    intro x; rfl
  have hker_iff : ∀ (x : FracIdealsCoprime K m),
    x ∈ chi.kernelSubgroup ↔
      FracIdealsCoprime.inclusion K m' m h x ∈ chi'.kernelSubgroup := by
    intro x
    simp only [RayClassChar.kernelSubgroup, Subgroup.mem_comap, MonoidHom.mem_ker]
    constructor
    · intro hx
      rw [← hmapOfDvd_eq]
      rw [IsInducedBy] at hind
      rwa [hind, MonoidHom.comp_apply] at hx
    · intro hx'
      rw [IsInducedBy] at hind
      rwa [hind, MonoidHom.comp_apply, hmapOfDvd_eq]
  unfold CongruenceSubgroupPair.IsEquiv CongruenceSubgroupPair.toAmbientSubgroup
  simp only [RayClassChar.kernelCongruenceSubgroup]
  ext I
  simp only [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  ·
    rintro ⟨hIm, ⟨J', hJ'_ker, hJ'_eq⟩⟩
    refine ⟨FracIdealsCoprime_subgroup_le K m' m h hIm, ?_⟩
    refine ⟨⟨I, hIm⟩, ?_, rfl⟩
    have hJ'_eq_incl : J' = FracIdealsCoprime.inclusion K m' m h ⟨I, hIm⟩ := by
      have := hincl_subtype ⟨I, hIm⟩
      exact Subtype.val_injective (hJ'_eq.trans this.symm)
    exact (hker_iff ⟨I, hIm⟩).mpr (hJ'_eq_incl ▸ hJ'_ker)
  ·
    rintro ⟨hIm', ⟨J, hJ_ker, hJ_eq⟩⟩
    have hIm : I ∈ FracIdealsCoprime_subgroup K m := by
      rw [← hJ_eq]; exact J.2
    refine ⟨hIm, ?_⟩
    refine ⟨⟨I, FracIdealsCoprime_subgroup_le K m' m h hIm⟩, ?_, rfl⟩
    have hincl_eq : FracIdealsCoprime.inclusion K m' m h J =
      ⟨I, FracIdealsCoprime_subgroup_le K m' m h hIm⟩ := by
      apply Subtype.val_injective
      exact hJ_eq
    rw [← hincl_eq]
    exact (hker_iff J).mp hJ_ker

end RayClassField

namespace RayClassField

/--
[mapOfDvd_ker_le_chi_ker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm2214.lean)
-/
@[path]
lemma mapOfDvd_ker_le_chi_ker
  {K : Type u}
  [Field K]
  [NumberField K]
  {m : Modulus K}
  {chi : RayClassChar K m} :
-- imply
  (RayClassGroup.mapOfDvd chi.conductor_dvd).ker ≤ chi.ker := by
-- proof
  obtain ⟨p', hp'mod, hp'equiv⟩ :=
    conductorModulus_exists_equiv chi.kernelCongruenceSubgroup
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (RayGroup K m) x
  have hmapOfDvd_eq : RayClassGroup.mapOfDvd chi.conductor_dvd
    ((QuotientGroup.mk' (RayGroup K m)) a) =
    (QuotientGroup.mk' (RayGroup K chi.conductor))
      (FracIdealsCoprime.inclusion K chi.conductor m chi.conductor_dvd a) := by
    show QuotientGroup.map _ _ _ _ ((QuotientGroup.mk' _) a) = (QuotientGroup.mk' _) _
    rw [QuotientGroup.map_mk']; rfl
  rw [hmapOfDvd_eq] at hx
  have ha_in_ray : FracIdealsCoprime.inclusion K chi.conductor m chi.conductor_dvd a ∈
    RayGroup K chi.conductor :=
    (QuotientGroup.eq_one_iff _).mp hx
  have hsubtype_eq : ((FracIdealsCoprime_subgroup K chi.conductor).subtype
    (FracIdealsCoprime.inclusion K chi.conductor m chi.conductor_dvd a) : (FracIdeal K)ˣ) =
    (FracIdealsCoprime_subgroup K m).subtype a := rfl
  have ha_val_in_p'_ambient : (FracIdealsCoprime_subgroup K m).subtype a ∈
    p'.toAmbientSubgroup := by
    suffices h : (FracIdealsCoprime_subgroup K m).subtype a ∈
      (RayGroup K p'.modulus).map (FracIdealsCoprime_subgroup K p'.modulus).subtype by
      exact Subgroup.map_mono p'.ray_le h
    rw [← hsubtype_eq]
    have hp'mod' : chi.conductor = p'.modulus := hp'mod.symm
    rw [show (RayGroup K p'.modulus).map (FracIdealsCoprime_subgroup K p'.modulus).subtype =
      (RayGroup K chi.conductor).map (FracIdealsCoprime_subgroup K chi.conductor).subtype from by
      rw [hp'mod']]
    exact Subgroup.mem_map_of_mem _ ha_in_ray
  have ha_in_lhs : (FracIdealsCoprime_subgroup K m).subtype a ∈
    (FracIdealsCoprime_subgroup K m ⊓ p'.toAmbientSubgroup : Subgroup (FracIdeal K)ˣ) :=
    ⟨a.2, ha_val_in_p'_ambient⟩
  have hisEquiv : (FracIdealsCoprime_subgroup K m ⊓ p'.toAmbientSubgroup : Subgroup _) =
    (FracIdealsCoprime_subgroup K p'.modulus ⊓
      chi.kernelCongruenceSubgroup.toAmbientSubgroup : Subgroup _) := by
    exact hp'equiv
  rw [hisEquiv] at ha_in_lhs
  have ha_in_ker_ambient := ha_in_lhs.2
  change (FracIdealsCoprime_subgroup K m).subtype a ∈
    chi.kernelSubgroup.map (FracIdealsCoprime_subgroup K m).subtype at ha_in_ker_ambient
  rw [Subgroup.mem_map] at ha_in_ker_ambient
  obtain ⟨b, hb_ker, hb_eq⟩ := ha_in_ker_ambient
  have hab : b = a := Subtype.val_injective hb_eq
  subst hab
  exact hb_ker

end RayClassField

namespace RayClassField

/--
[exists_primitive_inducing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm2214.lean)
-/
@[path]
lemma exists_primitive_inducing
  {K : Type u}
  [Field K]
  [NumberField K]
  {m : Modulus K}
  {chi : RayClassChar K m} :
-- imply
  ∃ (chi_prim : RayClassChar K chi.conductor), chi_prim.kernelCongruenceSubgroup.IsPrimitive ∧ IsInducedBy K chi.conductor m chi.conductor_dvd chi_prim chi := by
-- proof
  let f := RayClassGroup.mapOfDvd chi.conductor_dvd
  have hf_surj := RayClassGroup.mapOfDvd_surjective chi.conductor_dvd
  have hker := mapOfDvd_ker_le_chi_ker chi
  let f_inv := Function.surjInv hf_surj
  have hf_inv : Function.RightInverse f_inv (⇑f) := Function.rightInverse_surjInv hf_surj
  let g : { g : RayClassGroup K m →* ℂˣ // f.ker ≤ g.ker } := ⟨chi, hker⟩
  let chi_prim : RayClassChar K chi.conductor :=
    f.liftOfRightInverse f_inv hf_inv g
  have hcomp : chi_prim.comp f = chi := by
    have := f.liftOfRightInverse_comp (f_inv := f_inv) hf_inv g
    exact this
  refine ⟨chi_prim, ?_, ?_⟩
  ·
    have hind : IsInducedBy K chi.conductor m chi.conductor_dvd chi_prim chi := by
      show chi = chi_prim.comp f
      exact hcomp.symm
    have hequiv := isEquiv_kernel_of_induced chi chi_prim chi.conductor_dvd hind
    have hcond_eq : chi.kernelCongruenceSubgroup.conductor =
      chi_prim.kernelCongruenceSubgroup.conductor :=
      CongruenceSubgroupPair.conductor_eq_of_equiv
        chi.kernelCongruenceSubgroup chi_prim.kernelCongruenceSubgroup hequiv
    show chi_prim.kernelCongruenceSubgroup.modulus = chi_prim.kernelCongruenceSubgroup.conductor
    rw [show chi_prim.kernelCongruenceSubgroup.conductor =
      chi.kernelCongruenceSubgroup.conductor from hcond_eq.symm]
    rfl
  ·
    show chi = chi_prim.comp f
    exact hcomp.symm

end RayClassField

namespace RayClassField

/--
[kernel_isPrimitive_iff_modulus_eq_conductor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm2214.lean)
-/
@[path]
lemma kernel_isPrimitive_iff_modulus_eq_conductor
  {K : Type u}
  [Field K]
  [NumberField K]
  {m : Modulus K}
  {chi : RayClassChar K m} :
-- imply
  chi.kernelCongruenceSubgroup.IsPrimitive ↔ m = chi.conductor := by
-- proof
  rfl

end RayClassField

namespace RayClassField

/--
[conductor_dvd_of_inducing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm2214.lean)
-/
@[path]
lemma conductor_dvd_of_inducing
  {K : Type u}
  [Field K]
  [NumberField K]
  {m m' : Modulus K}
  {chi : RayClassChar K m}
  {chi' : RayClassChar K m'}
-- given
  (h : m'.dvd m)
  (hind : IsInducedBy K m' m h chi' chi) :
-- imply
  chi.conductor.dvd m' := by
-- proof
  have hequiv := isEquiv_kernel_of_induced chi chi' h hind
  exact chi.kernelCongruenceSubgroup.conductor_dvd_of_equiv
    chi'.kernelCongruenceSubgroup hequiv

end RayClassField

namespace RayClassField

/--
[RayClassChar.isPrimitive_iff_kernel_isPrimitive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm2214.lean)
-/
@[path]
lemma RayClassChar.isPrimitive_iff_kernel_isPrimitive
  {K : Type u}
  [Field K]
  [NumberField K]
  {m : Modulus K}
  {chi : RayClassChar K m} :
-- imply
  chi.IsPrimitive ↔ chi.kernelCongruenceSubgroup.IsPrimitive := by
-- proof
  constructor
  ·
    intro hprim
    obtain ⟨chi_prim, hkerprim, hind⟩ := exists_primitive_inducing chi
    have hcm : chi.conductor = m := hprim chi.conductor chi.conductor_dvd chi_prim hind
    rwa [kernel_isPrimitive_iff_modulus_eq_conductor]
  ·
    intro hker
    rw [kernel_isPrimitive_iff_modulus_eq_conductor] at hker
    intro m' hm'_dvd chi' hind
    have hc_dvd_m' : chi.conductor.dvd m' := conductor_dvd_of_inducing chi chi' hm'_dvd hind
    have hm_dvd_m' : m.dvd m' := hker ▸ hc_dvd_m'
    exact Modulus.dvd_antisymm m' m hm'_dvd hm_dvd_m'

end RayClassField


-- created on 2026-10-23
