/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.LieGroups.code.MaximalQuotients
import Lemma.Int.Any_EqUeaAction
import Lemma.Fin.Any_Eq.of.Ne_0
import Lemma.Complex.Any_Any_And_All_Eq_AdjointAction.All_Finite.of.IsHarishChandraBimodule.IsIrreducible
import Def.v1.Atlas.LieGroups.code.HighestWeightModules.Part2
import Theorem.v1.Atlas.LieGroups.code.HarishChandraCorollaries
import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part2


noncomputable section

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

theorem ueaScalarsSubmodule_fg : (ueaScalarsSubmodule (R := R) (𝔤 := 𝔤)).FG := by
  rw [ueaScalarsSubmodule, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

theorem ueaAdLocallyFinite [Module.Finite R 𝔤]
    (u : UniversalEnvelopingAlgebra R 𝔤) :
    ∃ (S : Submodule R (UniversalEnvelopingAlgebra R 𝔤)),
      Module.Finite R S ∧ u ∈ S ∧
      (∀ (x : 𝔤) (v : UniversalEnvelopingAlgebra R 𝔤), v ∈ S →
        (UniversalEnvelopingAlgebra.ι R x * v - v * UniversalEnvelopingAlgebra.ι R x) ∈ S) := by
  induction u using UniversalEnvelopingAlgebra.induction with
  | halg r =>
    refine ⟨ueaScalarsSubmodule, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]; exact ueaScalarsSubmodule_fg
    · exact ⟨r, rfl⟩
    · intro x v hv
      obtain ⟨c, rfl⟩ := hv
      have : UniversalEnvelopingAlgebra.ι R x * Algebra.linearMap R (UniversalEnvelopingAlgebra R 𝔤) c -
             Algebra.linearMap R (UniversalEnvelopingAlgebra R 𝔤) c * UniversalEnvelopingAlgebra.ι R x = 0 := by
        simp [Algebra.linearMap_apply, Algebra.commutes]
      rw [this]
      exact ⟨0, map_zero _⟩
  | hι y =>
    refine ⟨ueaIotaRange ⊔ ueaScalarsSubmodule, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]; exact ueaIotaRange_fg.sup ueaScalarsSubmodule_fg
    · exact Submodule.mem_sup_left (LinearMap.mem_range_self _ y)
    · intro x v hv
      rw [Submodule.mem_sup] at hv
      obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := hv
      rw [uea_ad_add]
      apply Submodule.add_mem
      · obtain ⟨z, rfl⟩ := hv₁
        show UniversalEnvelopingAlgebra.ι R x *
          (UniversalEnvelopingAlgebra.ι R : 𝔤 →ₗ⁅R⁆ _).toLinearMap z -
          (UniversalEnvelopingAlgebra.ι R : 𝔤 →ₗ⁅R⁆ _).toLinearMap z *
          UniversalEnvelopingAlgebra.ι R x ∈ _
        simp only [LieHom.coe_toLinearMap]
        rw [uea_comm_rel]
        exact Submodule.mem_sup_left (LinearMap.mem_range_self _ ⁅x, z⁆)
      · obtain ⟨c, rfl⟩ := hv₂
        have : UniversalEnvelopingAlgebra.ι R x * Algebra.linearMap R (UniversalEnvelopingAlgebra R 𝔤) c -
               Algebra.linearMap R (UniversalEnvelopingAlgebra R 𝔤) c * UniversalEnvelopingAlgebra.ι R x = 0 := by
          simp [Algebra.linearMap_apply, Algebra.commutes]
        rw [this]
        exact Submodule.zero_mem _
  | hadd a b iha ihb =>
    obtain ⟨Sa, hSa_fin, ha_mem, hSa_stab⟩ := iha
    obtain ⟨Sb, hSb_fin, hb_mem, hSb_stab⟩ := ihb
    refine ⟨Sa ⊔ Sb, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]
      exact (Module.Finite.iff_fg.mp hSa_fin).sup (Module.Finite.iff_fg.mp hSb_fin)
    · exact Submodule.add_mem _ (Submodule.mem_sup_left ha_mem) (Submodule.mem_sup_right hb_mem)
    · intro x v hv
      rw [Submodule.mem_sup] at hv
      obtain ⟨va, hva, vb, hvb, rfl⟩ := hv
      rw [uea_ad_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (hSa_stab x va hva))
        (Submodule.mem_sup_right (hSb_stab x vb hvb))
  | hmul a b iha ihb =>
    obtain ⟨Sa, hSa_fin, ha_mem, hSa_stab⟩ := iha
    obtain ⟨Sb, hSb_fin, hb_mem, hSb_stab⟩ := ihb
    refine ⟨Sa * Sb, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]
      exact (Module.Finite.iff_fg.mp hSa_fin).mul (Module.Finite.iff_fg.mp hSb_fin)
    · exact Submodule.mul_mem_mul ha_mem hb_mem
    · intro x v hv
      refine Submodule.mul_induction_on hv ?_ ?_
      · intro sa hsa sb hsb
        rw [uea_ad_leibniz]
        exact Submodule.add_mem _ (Submodule.mul_mem_mul (hSa_stab x sa hsa) hsb)
          (Submodule.mul_mem_mul hsa (hSb_stab x sb hsb))
      · intro v₁ v₂ hv₁ hv₂
        rw [uea_ad_add]
        exact Submodule.add_mem _ hv₁ hv₂

theorem ueaAction_adjoint_intertwine
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (act : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M), act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (x : 𝔤) (u : UniversalEnvelopingAlgebra R 𝔤) :
    adjointActionOnHom M M x (act u) =
    act (UniversalEnvelopingAlgebra.ι R x * u - u * UniversalEnvelopingAlgebra.ι R x) := by
  ext m
  simp only [adjointActionOnHom, LinearMap.coe_mk, AddHom.coe_mk, map_sub, map_mul,
    LinearMap.sub_apply]
  change ⁅x, (act u) m⁆ - (act u) ⁅x, m⁆ =
    act (UniversalEnvelopingAlgebra.ι R x) ((act u) m) - (act u) (act (UniversalEnvelopingAlgebra.ι R x) m)
  rw [hcompat x ((act u) m), hcompat x m]

theorem adjointActionOnHom_left_comp
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (x : 𝔤) (f : N →ₗ[R] N) (T : M →ₗ[R] N) :
    adjointActionOnHom M N x (f.comp T) =
    (adjointActionOnHom N N x f).comp T + f.comp (adjointActionOnHom M N x T) := by
  ext m
  simp [adjointActionOnHom, LinearMap.comp_apply, LinearMap.add_apply]

theorem adjointActionOnHom_right_comp
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (x : 𝔤) (T : M →ₗ[R] N) (g : M →ₗ[R] M) :
    adjointActionOnHom M N x (T.comp g) =
    (adjointActionOnHom M N x T).comp g + T.comp (adjointActionOnHom M M x g) := by
  ext m
  simp [adjointActionOnHom, LinearMap.comp_apply, LinearMap.add_apply]

theorem ueaAction_preserves_HomFin [Module.Finite R 𝔤]
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (u : UniversalEnvelopingAlgebra R 𝔤) (T : M →ₗ[R] N)
    (hT : T ∈ HomFin (R := R) (𝔤 := 𝔤) M N) :
    (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N) u).comp T ∈
      HomFin (R := R) (𝔤 := 𝔤) M N ∧
    T.comp (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M) u) ∈
      HomFin (R := R) (𝔤 := 𝔤) M N := by
  obtain ⟨S_T, hfin_T, hT_mem, hT_stab⟩ := hT
  obtain ⟨S_u, hfin_u, hu_mem, hu_stab⟩ := ueaAdLocallyFinite (R := R) (𝔤 := 𝔤) u
  let actN := UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N)
  let actM := UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M)
  have hcompatN : ∀ (y : 𝔤) (n : N), actN (UniversalEnvelopingAlgebra.ι R y) n = ⁅y, n⁆ := by
    intro y n; simp [actN, LieModule.toEnd_apply_apply]
  have hcompatM : ∀ (y : 𝔤) (m : M), actM (UniversalEnvelopingAlgebra.ι R y) m = ⁅y, m⁆ := by
    intro y m; simp [actM, LieModule.toEnd_apply_apply]

  let compBilinL : (N →ₗ[R] N) →ₗ[R] (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] N) :=
    LinearMap.llcomp R M N N
  let compBilinR : (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] M) →ₗ[R] (M →ₗ[R] N) :=
    { toFun := fun T' => {
        toFun := fun g => T'.comp g
        map_add' := fun g₁ g₂ => by ext; simp [LinearMap.comp_apply, LinearMap.add_apply]
        map_smul' := fun r g => by ext; simp [LinearMap.comp_apply, LinearMap.smul_apply] }
      map_add' := fun T₁ T₂ => by ext g m; simp [LinearMap.add_apply]
      map_smul' := fun r T₁ => by ext g m; simp [LinearMap.smul_apply] }
  let imgS_uN := S_u.map actN.toLinearMap
  let imgS_uM := S_u.map actM.toLinearMap
  let W_left := Submodule.map₂ compBilinL imgS_uN S_T
  let W_right := Submodule.map₂ compBilinR S_T imgS_uM

  have hfin_imgN : imgS_uN.FG := (Module.Finite.iff_fg.mp (Module.Finite.map S_u actN.toLinearMap))
  have hfin_imgM : imgS_uM.FG := (Module.Finite.iff_fg.mp (Module.Finite.map S_u actM.toLinearMap))
  have hfin_ST : S_T.FG := Module.Finite.iff_fg.mp hfin_T

  have imgN_stab : ∀ (x : 𝔤) (f : N →ₗ[R] N), f ∈ imgS_uN →
      adjointActionOnHom N N x f ∈ imgS_uN := by
    intro x f hf
    obtain ⟨v, hv_mem, rfl⟩ := Submodule.mem_map.mp hf
    simp only [AlgHom.toLinearMap_apply]
    rw [ueaAction_adjoint_intertwine N actN hcompatN x v]
    exact Submodule.mem_map_of_mem (hu_stab x v hv_mem)

  have imgM_stab : ∀ (x : 𝔤) (g : M →ₗ[R] M), g ∈ imgS_uM →
      adjointActionOnHom M M x g ∈ imgS_uM := by
    intro x g hg
    obtain ⟨v, hv_mem, rfl⟩ := Submodule.mem_map.mp hg
    simp only [AlgHom.toLinearMap_apply]
    rw [ueaAction_adjoint_intertwine M actM hcompatM x v]
    exact Submodule.mem_map_of_mem (hu_stab x v hv_mem)
  constructor
  ·
    show IsFiniteTypeMap (𝔤 := 𝔤) M N ((actN u).comp T)
    refine ⟨W_left, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]; exact hfin_imgN.map₂ compBilinL hfin_ST
    · exact Submodule.apply_mem_map₂ compBilinL (Submodule.mem_map_of_mem hu_mem) hT_mem
    ·
      intro x w hw


      have hW_left_le : W_left ≤ W_left.comap
          ({ toFun := adjointActionOnHom M N x
             map_add' := fun f g => by ext m; simp [adjointActionOnHom, lie_add, sub_add_sub_comm]
             map_smul' := fun c f => by ext m; simp [adjointActionOnHom, lie_smul, smul_sub]
           } : (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] N)) := by
        rw [Submodule.map₂_le]
        intro f hf T' hT'

        show adjointActionOnHom M N x (compBilinL f T') ∈ W_left
        change adjointActionOnHom M N x (f.comp T') ∈ W_left
        rw [adjointActionOnHom_left_comp M N x f T']


        apply W_left.add_mem
        · exact Submodule.apply_mem_map₂ compBilinL (imgN_stab x f hf) hT'
        · exact Submodule.apply_mem_map₂ compBilinL hf (hT_stab x T' hT')
      exact hW_left_le hw
  ·
    show IsFiniteTypeMap (𝔤 := 𝔤) M N (T.comp (actM u))
    refine ⟨W_right, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]; exact hfin_ST.map₂ compBilinR hfin_imgM
    · exact Submodule.apply_mem_map₂ compBilinR hT_mem (Submodule.mem_map_of_mem hu_mem)
    · intro x w hw
      have hW_right_le : W_right ≤ W_right.comap
          ({ toFun := adjointActionOnHom M N x
             map_add' := fun f g => by ext m; simp [adjointActionOnHom, lie_add, sub_add_sub_comm]
             map_smul' := fun c f => by ext m; simp [adjointActionOnHom, lie_smul, smul_sub]
           } : (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] N)) := by
        rw [Submodule.map₂_le]
        intro T' hT' g hg
        show adjointActionOnHom M N x (compBilinR T' g) ∈ W_right
        change adjointActionOnHom M N x (T'.comp g) ∈ W_right
        rw [adjointActionOnHom_right_comp M N x T' g]
        apply W_right.add_mem
        · exact Submodule.apply_mem_map₂ compBilinR (hT_stab x T' hT') hg
        · exact Submodule.apply_mem_map₂ compBilinR hT' (imgM_stab x g hg)
      exact hW_right_le hw

theorem leftAction_preserves_HomFin [Module.Finite R 𝔤]
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (u : UniversalEnvelopingAlgebra R 𝔤) (T : M →ₗ[R] N)
    (hT : T ∈ HomFin (R := R) (𝔤 := 𝔤) M N) :
    (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N) u).comp T ∈
      HomFin (R := R) (𝔤 := 𝔤) M N :=
  (ueaAction_preserves_HomFin M N u T hT).1

theorem rightAction_preserves_HomFin [Module.Finite R 𝔤]
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (u : UniversalEnvelopingAlgebra R 𝔤) (T : M →ₗ[R] N)
    (hT : T ∈ HomFin (R := R) (𝔤 := 𝔤) M N) :
    T.comp (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M) u) ∈
      HomFin (R := R) (𝔤 := 𝔤) M N :=
  (ueaAction_preserves_HomFin M N u T hT).2

end
