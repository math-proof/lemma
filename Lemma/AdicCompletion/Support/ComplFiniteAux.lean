import Mathlib
import Lemma.AdicCompletion.RingHom.eq.of.Map.MaximalIdeal.le.of.forall.Apply.AlgebraMap.eq
import Lemma.AdicCompletion.exists.RingEquiv.of.IsLocalization.AtPrime.of.IsMaximal

open IsLocalRing
open scoped TensorProduct Pointwise

/-! FLT ComplFiniteAux + LocalRing kernel helpers for
`exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal`. -/

namespace AdicCompletion

section Kernel

variable {A : Type*} [CommRing A] (I : Ideal A)

theorem isUnit_one_add_of_mem_map (hI : I.FG) {x : AdicCompletion I A}
    (hx : x ∈ I.map (algebraMap A (AdicCompletion I A))) : IsUnit (1 + x) := by
  have : IsAdicComplete (I.map (algebraMap A (AdicCompletion I A))) (AdicCompletion I A) :=
    isAdicComplete_self I hI
  have h := Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot _ hx) 1
  rwa [mul_one, add_comm] at h

end Kernel

namespace ComplFiniteAux

section Generic

theorem semilocalComponent_completionBaseChangeHom {O C : Type*} [CommRing O] [CommRing C]
    [Algebra O C] (p : Ideal O) (𝔫 : Ideal C) [𝔫.LiesOver p]
    (h : p.map (algebraMap O C) ≤ 𝔫) (a : AdicCompletion p O) :
    semilocalComponent (p.map (algebraMap O C)) h (completionBaseChangeHom C p a) =
      algebraMap (AdicCompletion p O) (AdicCompletion 𝔫 C) a := by
  refine ext_evalₐ fun n => ?_
  obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective (evalₐ p n a)
  have hL : evalₐ 𝔫 n (semilocalComponent (p.map (algebraMap O C)) h
      (completionBaseChangeHom C p a)) =
      Ideal.Quotient.mk (𝔫 ^ n) (algebraMap O C o) := by
    rw [semilocalComponent, completionBaseChangeHom, evalₐ_mapₐ, evalₐ_mapₐ, ← ho,
      levelMapₐ_mk, levelMapₐ_mk]
    simp [Algebra.ofId_apply]
  have hR : evalₐ 𝔫 n (algebraMap (AdicCompletion p O) (AdicCompletion 𝔫 C) a) =
      Ideal.Quotient.mk (𝔫 ^ n) (algebraMap O C o) :=
    evalₐ_algebraMap_of_liesOver p 𝔫 n o a ho.symm
  exact hL.trans hR.symm

theorem tensorRingHom_surjective {O : Type*} [CommRing O] (C : Type*) [CommRing C] [Algebra O C]
    [Module.Finite O C] (p : Ideal O) : Function.Surjective (tensorRingHom C p) := by
  intro t
  obtain ⟨z, hz⟩ := ofTensorProduct_surjective_of_finite p C (restrictScalarsEquiv C p t)
  refine ⟨z, (restrictScalarsEquiv C p).injective ?_⟩
  rw [restrictScalarsEquiv_tensorRingHom, hz]

noncomputable def proj {O C : Type*} [CommRing O] [CommRing C]
    [Algebra O C] (p : Ideal O) (𝔫 : Ideal C) [𝔫.LiesOver p]
    (h : p.map (algebraMap O C) ≤ 𝔫) :
    (AdicCompletion p O ⊗[O] C) →ₗ[AdicCompletion p O] AdicCompletion 𝔫 C :=
  { toFun := fun z => semilocalComponent (p.map (algebraMap O C)) h (tensorRingHom C p z)
    map_add' := fun x y => by simp only [map_add]
    map_smul' := fun a z => by
      induction z using TensorProduct.inductionOn with
      | tmul x b =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, tensorRingHom_tmul, tensorRingHom_tmul,
          map_mul (completionBaseChangeHom C p), mul_assoc,
          map_mul (semilocalComponent (p.map (algebraMap O C)) h) (completionBaseChangeHom C p a),
          semilocalComponent_completionBaseChangeHom, RingHom.id_apply, Algebra.smul_def]
      | add u v hu hv => simp only [smul_add, map_add, hu, hv] }

theorem proj_apply {O C : Type*} [CommRing O] [CommRing C]
    [Algebra O C] (p : Ideal O) (𝔫 : Ideal C) [𝔫.LiesOver p]
    (h : p.map (algebraMap O C) ≤ 𝔫) (z : AdicCompletion p O ⊗[O] C) :
    proj p 𝔫 h z = semilocalComponent (p.map (algebraMap O C)) h (tensorRingHom C p z) := rfl

theorem finite_of_semilocalComponent_surjective {O C : Type*} [CommRing O] [CommRing C]
    [Algebra O C] [Module.Finite O C] (p : Ideal O) (𝔫 : Ideal C) [𝔫.LiesOver p]
    (h : p.map (algebraMap O C) ≤ 𝔫)
    (hψ : Function.Surjective (semilocalComponent (p.map (algebraMap O C)) h)) :
    Module.Finite (AdicCompletion p O) (AdicCompletion 𝔫 C) :=
  Module.Finite.of_surjective (proj p 𝔫 h) (hψ.comp (tensorRingHom_surjective C p))

end Generic

theorem isNoetherianRing_of_moduleFinite (B C : Type*) [CommRing B] [IsNoetherianRing B]
    [CommRing C] [Algebra B C] [Module.Finite B C] : IsNoetherianRing C :=
  isNoetherian_of_tower B (S := C) (M := C) inferInstance

section Setting

universe u

variable (B : Type u) {C : Type u} [CommRing B] [IsNoetherianRing B] [CommRing C] [Algebra B C]
  [Module.Finite B C] (𝔫 : Ideal C) [𝔫.IsMaximal]

local notation "J" => Ideal.comap (algebraMap B C) 𝔫
local notation "B̂" => AdicCompletion (Ideal.comap (algebraMap B C) 𝔫) B
local notation "Ĉ" => AdicCompletion 𝔫 C

omit [IsNoetherianRing B] [Module.Finite B C] [𝔫.IsMaximal] in
theorem liesOver : 𝔫.LiesOver J := ⟨rfl⟩

omit [IsNoetherianRing B] in
theorem isMaximal_J : (J).IsMaximal := by
  have : Algebra.IsIntegral B C := inferInstance
  exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔫

omit [IsNoetherianRing B] [Module.Finite B C] [𝔫.IsMaximal] in
theorem map_J_le : (J).map (algebraMap B C) ≤ 𝔫 := Ideal.map_comap_le

omit [IsNoetherianRing B] in
theorem isArtinianRing_fibre : IsArtinianRing (C ⧸ (J).map (algebraMap B C)) := by
  have : (J).IsMaximal := isMaximal_J B 𝔫
  let : Field (B ⧸ J) := Ideal.Quotient.field J
  have : Module.Finite (B ⧸ J) (C ⧸ (J).map (algebraMap B C)) :=
    Module.Finite.of_restrictScalars_finite B _ _
  exact IsArtinianRing.of_finite (B ⧸ J) _

omit [IsNoetherianRing B] [Module.Finite B C] in
abbrev idx : {P : Ideal C // P.IsMaximal ∧ (J).map (algebraMap B C) ≤ P} :=
  ⟨𝔫, ‹𝔫.IsMaximal›, map_J_le B 𝔫⟩

theorem moduleFinite :
    letI := liesOver B 𝔫
    Module.Finite B̂ Ĉ := by
  have := liesOver B 𝔫
  have : IsNoetherianRing C := isNoetherianRing_of_moduleFinite B C
  have : IsArtinianRing (C ⧸ (J).map (algebraMap B C)) := isArtinianRing_fibre B 𝔫
  refine finite_of_semilocalComponent_surjective (J) 𝔫 (map_J_le B 𝔫) ?_
  classical
  intro y
  obtain ⟨x, hx⟩ := AdicCompletion.semilocalPiHom_surjective ((J).map (algebraMap B C))
    (Function.update 0 (idx B 𝔫) y)
  refine ⟨x, ?_⟩
  have hP := congrFun hx (idx B 𝔫)
  rw [AdicCompletion.semilocalPiHom_apply, Function.update_self] at hP
  exact hP

omit [Module.Finite B C] [𝔫.IsMaximal] in
theorem fg_J : (J).FG := IsNoetherian.noetherian _

omit [Module.Finite B C] [𝔫.IsMaximal] in
theorem map_eq_ker : (J).map (algebraMap B B̂) = RingHom.ker (evalₐ (J) 1) := by
  rw [ker_evalₐ_eq_map_pow (J) (fg_J B 𝔫) 1, pow_one]

theorem isUnit_of_not_mem {x : B̂} (hx : x ∉ (J).map (algebraMap B B̂)) : IsUnit x := by
  have : (J).IsMaximal := isMaximal_J B 𝔫
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ (J) 1 x)
  have hbJ : b ∉ J := by
    intro hbJ
    apply hx
    rw [map_eq_ker B 𝔫, RingHom.mem_ker, ← hb, Ideal.Quotient.eq_zero_iff_mem, pow_one]
    exact hbJ
  obtain ⟨c, j, hj, hbc⟩ := Ideal.IsMaximal.exists_inv (isMaximal_J B 𝔫) hbJ
  have hmem : x * algebraMap B B̂ c - 1 ∈ (J).map (algebraMap B B̂) := by
    rw [map_eq_ker B 𝔫, RingHom.mem_ker, map_sub, map_mul, map_one, ← hb, evalₐ_algebraMap,
      ← map_mul, ← map_one (Ideal.Quotient.mk ((J) ^ 1)), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem, pow_one]
    have : b * c - 1 = -j := by rw [← hbc]; ring
    rw [this]; exact Submodule.neg_mem _ hj
  have hu : IsUnit (1 + (x * algebraMap B B̂ c - 1)) :=
    isUnit_one_add_of_mem_map (J) (fg_J B 𝔫) hmem
  rw [add_sub_cancel] at hu
  exact isUnit_of_mul_isUnit_left hu

omit [Module.Finite B C] in
theorem map_ne_top : (J).map (algebraMap B B̂) ≠ ⊤ := by
  intro h
  rw [map_eq_ker B 𝔫, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one, eq_comm,
    Ideal.Quotient.zero_eq_one_iff, pow_one, Ideal.comap_eq_top_iff] at h
  exact (Ideal.IsMaximal.ne_top ‹𝔫.IsMaximal›) h

theorem isLocalRing_hat : IsLocalRing B̂ := by
  have : Nontrivial B̂ := by
    refine ⟨⟨0, 1, fun h => map_ne_top B 𝔫 ?_⟩⟩
    rw [Ideal.eq_top_iff_one, ← h]; exact Ideal.zero_mem _
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases ha : a ∈ (J).map (algebraMap B B̂)
  · right
    have hu := isUnit_one_add_of_mem_map (J) (fg_J B 𝔫) (Submodule.neg_mem _ ha)
    rwa [← sub_eq_add_neg] at hu
  · left; exact isUnit_of_not_mem B 𝔫 ha

theorem le_map_of_ne_top {I : Ideal B̂} (hI : I ≠ ⊤) : I ≤ (J).map (algebraMap B B̂) := by
  intro x hx
  by_contra hxm
  exact hI (Ideal.eq_top_of_isUnit_mem I hx (isUnit_of_not_mem B 𝔫 hxm))

section Retract

open scoped Classical

variable [IsNoetherianRing C]
  [IsArtinianRing (C ⧸ (Ideal.comap (algebraMap B C) 𝔫).map (algebraMap B C))]
  [𝔫.LiesOver (Ideal.comap (algebraMap B C) 𝔫)]

local notation "JC" => Ideal.map (algebraMap B C) (Ideal.comap (algebraMap B C) 𝔫)

omit [IsNoetherianRing B] [Module.Finite B C] [𝔫.IsMaximal] [IsNoetherianRing C]
  [IsArtinianRing (C ⧸ (Ideal.comap (algebraMap B C) 𝔫).map (algebraMap B C))]
  [𝔫.LiesOver (Ideal.comap (algebraMap B C) 𝔫)] in
abbrev fam : {P : Ideal C // P.IsMaximal ∧
    Ideal.map (algebraMap B C) (Ideal.comap (algebraMap B C) 𝔫) ≤ P} → Type u :=
  fun P => AdicCompletion (P : Ideal C) C

noncomputable def inclAdd : Ĉ →+ B̂ ⊗[B] C :=
  ((tensorRingEquiv C (J)).symm.toRingEquiv.toAddMonoidHom.comp
      (semilocalPiEquiv (JC)).symm.toAddMonoidHom).comp
    (AddMonoidHom.single (fam B 𝔫) (idx B 𝔫))

omit [𝔫.LiesOver (Ideal.comap (algebraMap B C) 𝔫)] in
theorem inclAdd_apply (y : Ĉ) :
    inclAdd B 𝔫 y = (tensorRingEquiv C (J)).symm
      ((semilocalPiEquiv (JC)).symm (Pi.single (M := fam B 𝔫) (idx B 𝔫) y)) := rfl

omit [IsNoetherianRing B] [Module.Finite B C] [IsNoetherianRing C]
  [IsArtinianRing (C ⧸ (Ideal.comap (algebraMap B C) 𝔫).map (algebraMap B C))]
  [𝔫.LiesOver (Ideal.comap (algebraMap B C) 𝔫)] in
theorem semilocalComponent_eq_apply (v : AdicCompletion (JC) C) :
    semilocalComponent (JC) (map_J_le B 𝔫) v = semilocalPiHom (JC) v (idx B 𝔫) := rfl

omit [𝔫.IsMaximal] [IsNoetherianRing C]
  [IsArtinianRing (C ⧸ (Ideal.comap (algebraMap B C) 𝔫).map (algebraMap B C))]
  [𝔫.LiesOver (Ideal.comap (algebraMap B C) 𝔫)] in
theorem tensorRingHom_symm (w : AdicCompletion (JC) C) :
    tensorRingHom C (J) ((tensorRingEquiv C (J)).symm w) = w :=
  (tensorRingEquiv C (J)).apply_symm_apply w

omit [IsNoetherianRing B] [Module.Finite B C] [𝔫.IsMaximal] [𝔫.LiesOver (Ideal.comap (algebraMap B C) 𝔫)] in
theorem semilocalPiHom_symm (v : (P : _) → fam B 𝔫 P) :
    semilocalPiHom (JC) ((semilocalPiEquiv (JC)).symm v) = v :=
  (semilocalPiEquiv (JC)).apply_symm_apply v

theorem proj_inclAdd (y : Ĉ) : proj (J) 𝔫 (map_J_le B 𝔫) (inclAdd B 𝔫 y) = y := by
  rw [proj_apply, inclAdd_apply, tensorRingHom_symm, semilocalComponent_eq_apply,
    semilocalPiHom_symm, Pi.single_eq_same]

omit [IsNoetherianRing B] [Module.Finite B C] [IsNoetherianRing C]
  [IsArtinianRing (C ⧸ (Ideal.comap (algebraMap B C) 𝔫).map (algebraMap B C))] in
theorem algebraMap_eq_apply (a : B̂) :
    algebraMap B̂ Ĉ a = semilocalPiHom (JC) (completionBaseChangeHom C (J) a) (idx B 𝔫) := by
  rw [← semilocalComponent_eq_apply, semilocalComponent_completionBaseChangeHom]

omit [IsNoetherianRing B] [Module.Finite B C] [𝔫.IsMaximal] [IsNoetherianRing C]
  [IsArtinianRing (C ⧸ (Ideal.comap (algebraMap B C) 𝔫).map (algebraMap B C))]
  [𝔫.LiesOver (Ideal.comap (algebraMap B C) 𝔫)] in
theorem of_one' : of (JC) C (1 : C) = 1 := by
  rw [show of (JC) C (1 : C) = algebraMap C (AdicCompletion (JC) C) 1 from rfl, map_one]

omit [𝔫.IsMaximal] [IsNoetherianRing C]
  [IsArtinianRing (C ⧸ (Ideal.comap (algebraMap B C) 𝔫).map (algebraMap B C))]
  [𝔫.LiesOver (Ideal.comap (algebraMap B C) 𝔫)] in
theorem tensorRingEquiv_symm_completionBaseChangeHom (a : B̂) :
    (tensorRingEquiv C (J)).symm (completionBaseChangeHom C (J) a) = a ⊗ₜ[B] (1 : C) := by
  rw [AlgEquiv.symm_apply_eq, tensorRingEquiv_tmul, of_one', mul_one]

omit [IsNoetherianRing B] [Module.Finite B C] [𝔫.IsMaximal] [IsNoetherianRing C]
  [IsArtinianRing (C ⧸ (Ideal.comap (algebraMap B C) 𝔫).map (algebraMap B C))]
  [𝔫.LiesOver (Ideal.comap (algebraMap B C) 𝔫)] in
theorem smul_eq_tmul_one_mul (a : B̂) (X : B̂ ⊗[B] C) : a • X = a ⊗ₜ[B] (1 : C) * X := by
  rw [Algebra.smul_def (A := B̂ ⊗[B] C), Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self_apply]

theorem inclAdd_smul (a : B̂) (y : Ĉ) : inclAdd B 𝔫 (a • y) = a • inclAdd B 𝔫 y := by
  have h1 : Pi.single (M := fam B 𝔫) (idx B 𝔫) (a • y) =
      semilocalPiHom (JC) (completionBaseChangeHom C (J) a) *
        Pi.single (M := fam B 𝔫) (idx B 𝔫) y := by
    rw [← Pi.single_mul_right]
    congr 1
    rw [Algebra.smul_def, algebraMap_eq_apply]
  have h2 : (semilocalPiEquiv (JC)).symm (Pi.single (M := fam B 𝔫) (idx B 𝔫) (a • y)) =
      completionBaseChangeHom C (J) a *
        (semilocalPiEquiv (JC)).symm (Pi.single (M := fam B 𝔫) (idx B 𝔫) y) := by
    rw [h1, map_mul]
    congr 1
    rw [RingEquiv.symm_apply_eq]
    rfl
  rw [inclAdd_apply, h2, map_mul, tensorRingEquiv_symm_completionBaseChangeHom, inclAdd_apply]
  exact (smul_eq_tmul_one_mul B 𝔫 a _).symm

noncomputable def inclₗ : Ĉ →ₗ[B̂] B̂ ⊗[B] C where
  toFun := inclAdd B 𝔫
  map_add' := (inclAdd B 𝔫).map_add
  map_smul' := inclAdd_smul B 𝔫

theorem flat [Module.Flat B C] : Module.Flat B̂ Ĉ :=
  Module.Flat.of_retract (inclₗ B 𝔫) (proj (J) 𝔫 (map_J_le B 𝔫))
    (LinearMap.ext fun y => proj_inclAdd B 𝔫 y)

omit [IsNoetherianRing B] [Module.Finite B C] [𝔫.IsMaximal] [IsNoetherianRing C]
  [IsArtinianRing (C ⧸ (Ideal.comap (algebraMap B C) 𝔫).map (algebraMap B C))]
  [𝔫.LiesOver (Ideal.comap (algebraMap B C) 𝔫)] in
theorem map_le_ker : (J).map (algebraMap B Ĉ) ≤ RingHom.ker (evalₐ 𝔫 1) := by
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap, RingHom.mem_ker, AdicCompletion.algebraMap_apply, evalₐ_of,
    Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact hb

theorem faithfullyFlat [Module.Flat B C] : Module.FaithfullyFlat B̂ Ĉ := by
  refine (Module.FaithfullyFlat.iff_flat_and_proper_ideal B̂ Ĉ).mpr ⟨flat B 𝔫, fun I hI htop => ?_⟩
  have hle : I • (⊤ : Submodule B̂ Ĉ) ≤ ((J).map (algebraMap B B̂)) • (⊤ : Submodule B̂ Ĉ) :=
    Submodule.smul_mono (le_map_of_ne_top B 𝔫 hI) le_rfl
  rw [htop, top_le_iff, Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff,
    Ideal.map_map, ← IsScalarTower.algebraMap_eq] at hle
  have h1 : (1 : Ĉ) ∈ RingHom.ker (evalₐ 𝔫 1) := map_le_ker B 𝔫 (hle ▸ Submodule.mem_top)
  rw [RingHom.mem_ker, map_one, eq_comm, Ideal.Quotient.zero_eq_one_iff, pow_one] at h1
  exact Ideal.IsMaximal.ne_top ‹𝔫.IsMaximal› h1

theorem injective [Module.Flat B C] : Function.Injective (algebraMap B̂ Ĉ) := by
  have := faithfullyFlat B 𝔫
  exact FaithfulSMul.algebraMap_injective B̂ Ĉ

end Retract

end Setting

end ComplFiniteAux

end AdicCompletion
