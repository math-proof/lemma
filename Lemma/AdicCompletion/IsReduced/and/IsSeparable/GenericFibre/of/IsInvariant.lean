import sympy.Basic
import sympy.Flt
import Mathlib

open IsLocalRing

/--
[AdicCompletion_isReduced_and_isSeparable_genericFibre_of_isInvariant](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdicCompletion_isReduced_and_isSeparable_genericFibre_of_isInvariant.lean)
-/
@[path]
private lemma main
  {O C G : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] [CommRing C] [IsDomain C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C] [Group G] [Finite G] [MulSemiringAction G C] [SMulCommClass G O C] [FaithfulSMul G C] [Algebra.IsInvariant O C G]
-- given
  (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)] (K₀ : Type) [Field K₀] [Algebra (AdicCompletion (maximalIdeal O) O) K₀] [IsFractionRing (AdicCompletion (maximalIdeal O) O) K₀] (F : Type) [CommRing F] [Algebra (AdicCompletion 𝔫 C) F] [Algebra (AdicCompletion (maximalIdeal O) O) F] [Algebra K₀ F] [IsScalarTower (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) F] [IsScalarTower (AdicCompletion (maximalIdeal O) O) K₀ F] [IsLocalization (Algebra.algebraMapSubmonoid (AdicCompletion 𝔫 C) (nonZeroDivisors (AdicCompletion (maximalIdeal O) O))) F] :
-- imply
  IsReduced F ∧ Algebra.IsSeparable K₀ F := by
-- proof
  classical

  have : IsNoetherianRing C := IsNoetherianRing.of_finite O C
  have hOC : Function.Injective (algebraMap O C) :=
    (faithfulSMul_iff_algebraMap_injective O C).mp inferInstance
  have : IsDomain O := Function.Injective.isDomain (algebraMap O C) hOC
  have : Module.IsTorsionFree O C := Module.IsTorsionFree.of_smul_eq_zero (fun o c h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    obtain h | h := h
    ·
      left; exact hOC (by rw [h, map_zero])
    ·
      right; exact h)

  let : Algebra (FractionRing O) (FractionRing C) := FractionRing.liftAlgebra O (FractionRing C)
  have : IsScalarTower O (FractionRing O) (FractionRing C) := inferInstance
  let : MulSemiringAction G (FractionRing C) :=
    IsFractionRing.mulSemiringAction G C (FractionRing C)
  have : IsGaloisGroup G O C := ⟨inferInstance, inferInstance, inferInstance⟩
  have : IsGaloisGroup G (FractionRing O) (FractionRing C) := IsGaloisGroup.toFractionRing G O C
  have : IsGalois (FractionRing O) (FractionRing C) :=
    IsGaloisGroup.isGalois G (FractionRing O) (FractionRing C)
  have : FiniteDimensional (FractionRing O) (FractionRing C) :=
    IsGaloisGroup.finiteDimensional G (FractionRing O) (FractionRing C)
  have : Algebra.FormallyUnramified (FractionRing O) (FractionRing C) :=
    Algebra.FormallyUnramified.of_isSeparable (FractionRing O) (FractionRing C)

  have hinjK₀ : Function.Injective (algebraMap (AdicCompletion (maximalIdeal O) O) K₀) :=
    IsFractionRing.injective (AdicCompletion (maximalIdeal O) O) K₀
  have : IsDomain (AdicCompletion (maximalIdeal O) O) := Function.Injective.isDomain _ hinjK₀
  have hinjO : Function.Injective (algebraMap O (AdicCompletion (maximalIdeal O) O)) := by
    have : (algebraMap O (AdicCompletion (maximalIdeal O) O) : O → AdicCompletion (maximalIdeal O) O) =
      AdicCompletion.of (maximalIdeal O) O := by
      funext o
      rw [AdicCompletion.algebraMap_apply (maximalIdeal O), Algebra.algebraMap_self, RingHom.id_apply]
    rw [this]
    exact AdicCompletion.of_injective (maximalIdeal O) O
  let algOK₀ : Algebra O K₀ :=
    ((algebraMap (AdicCompletion (maximalIdeal O) O) K₀).comp
      (algebraMap O (AdicCompletion (maximalIdeal O) O))).toAlgebra
  have : IsScalarTower O (AdicCompletion (maximalIdeal O) O) K₀ :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : FaithfulSMul O K₀ :=
    (faithfulSMul_iff_algebraMap_injective O K₀).mpr (hinjK₀.comp hinjO)
  let algKK₀ : Algebra (FractionRing O) K₀ := FractionRing.liftAlgebra O K₀
  have : IsScalarTower O (FractionRing O) K₀ := inferInstance
  let algOF : Algebra O F :=
    ((algebraMap (AdicCompletion (maximalIdeal O) O) F).comp
      (algebraMap O (AdicCompletion (maximalIdeal O) O))).toAlgebra
  have : IsScalarTower O (AdicCompletion (maximalIdeal O) O) F :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower O K₀ F := IsScalarTower.of_algebraMap_eq (fun o => by
    show algebraMap (AdicCompletion (maximalIdeal O) O) F (algebraMap O _ o) =
      algebraMap K₀ F (algebraMap (AdicCompletion (maximalIdeal O) O) K₀ (algebraMap O _ o))
    rw [← IsScalarTower.algebraMap_apply (AdicCompletion (maximalIdeal O) O) K₀ F])
  let algKF : Algebra (FractionRing O) F :=
    ((algebraMap K₀ F).comp (algebraMap (FractionRing O) K₀)).toAlgebra
  have : IsScalarTower (FractionRing O) K₀ F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower O (FractionRing O) F := IsScalarTower.of_algebraMap_eq (fun o => by
    show algebraMap O F o = algebraMap K₀ F (algebraMap (FractionRing O) K₀ (algebraMap O (FractionRing O) o))
    rw [← IsScalarTower.algebraMap_apply O (FractionRing O) K₀, ← IsScalarTower.algebraMap_apply O K₀ F])

  let gCF : C →+* F := (algebraMap (AdicCompletion 𝔫 C) F).comp (algebraMap C (AdicCompletion 𝔫 C))
  have hCĈ : ∀ c : C, algebraMap C (AdicCompletion 𝔫 C) c = AdicCompletion.of 𝔫 C c := by
    intro c
    rw [AdicCompletion.algebraMap_apply 𝔫, Algebra.algebraMap_self, RingHom.id_apply]
  have hsq : ∀ o : O, gCF (algebraMap O C o) = algebraMap O F o := by
    intro o
    show algebraMap (AdicCompletion 𝔫 C) F (algebraMap C (AdicCompletion 𝔫 C) (algebraMap O C o)) =
      algebraMap (AdicCompletion (maximalIdeal O) O) F (algebraMap O (AdicCompletion (maximalIdeal O) O) o)
    rw [IsScalarTower.algebraMap_apply (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) F,
      ← IsScalarTower.algebraMap_apply O (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C),
      AdicCompletion.algebraMap_apply 𝔫, AdicCompletion.algebraMap_apply 𝔫, Algebra.algebraMap_self,
      RingHom.id_apply]
  have hunit : ∀ y : nonZeroDivisors C, IsUnit (gCF y) := by
    intro y
    have hy0 : (y : C) ≠ 0 := nonZeroDivisors.ne_zero y.2
    have : Algebra.IsIntegral O C := Algebra.IsIntegral.of_finite O C
    obtain ⟨b, a, ha, hab⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul O (1 : C) hy0

    have h1 : gCF (algebraMap O C a) = gCF y * gCF b := by
      rw [← map_mul, ← hab, Algebra.smul_def, mul_one]
    have hu : IsUnit (gCF (algebraMap O C a)) := by
      rw [hsq, IsScalarTower.algebraMap_apply O K₀ F]
      refine (IsUnit.mk0 _ ?_).map _
      exact (map_ne_zero_iff (algebraMap O K₀) (hinjK₀.comp hinjO)).mpr ha
    rw [h1] at hu
    exact isUnit_of_mul_isUnit_left hu
  let φ₀ : FractionRing C →+* F := IsLocalization.lift (M := nonZeroDivisors C) hunit
  have hφ₀C : ∀ c : C, φ₀ (algebraMap C (FractionRing C) c) = gCF c :=
    fun c => IsLocalization.lift_eq hunit c
  have hφ₀K : ∀ k : FractionRing O, φ₀ (algebraMap (FractionRing O) (FractionRing C) k) =
      algebraMap (FractionRing O) F k := by
    have : φ₀.comp (algebraMap (FractionRing O) (FractionRing C)) = algebraMap (FractionRing O) F := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors O)
      ext o
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply O (FractionRing O) (FractionRing C),
        IsScalarTower.algebraMap_apply O C (FractionRing C), hφ₀C, hsq,
        ← IsScalarTower.algebraMap_apply O (FractionRing O) F]
    intro k
    exact congrArg (fun f : FractionRing O →+* F => f k) this
  let φ : AlgHom (FractionRing O) (FractionRing C) F := { toRingHom := φ₀, commutes' := hφ₀K }
  have hφC : ∀ c : C, φ (algebraMap C (FractionRing C) c) = gCF c := hφ₀C
  let ψ : AlgHom K₀ (TensorProduct (FractionRing O) K₀ (FractionRing C)) F :=
    Algebra.TensorProduct.lift (Algebra.ofId K₀ F) φ (fun _ _ => Commute.all _ _)
  have hψ : ∀ (k : K₀) (l : FractionRing C),
      ψ (TensorProduct.tmul (FractionRing O) k l) = algebraMap K₀ F k * φ l :=
    fun k l => Algebra.TensorProduct.lift_tmul _ _ _ k l

  set I : Ideal C := (maximalIdeal O).map (algebraMap O C) with hI
  have hI𝔫 : I ≤ 𝔫 := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro o ho
    rwa [Ideal.LiesOver.over (P := 𝔫) (p := maximalIdeal O)] at ho
  have : IsArtinianRing (C ⧸ I) := by
    let : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field (maximalIdeal O)
    have : Module.Finite (O ⧸ maximalIdeal O) (C ⧸ I) := inferInstance
    exact IsArtinianRing.of_finite (O ⧸ maximalIdeal O) (C ⧸ I)
  let Φ := AdicCompletion.semilocalPiEquiv I
  let T := AdicCompletion.tensorRingEquiv C (maximalIdeal O)
  let 𝔫' : Subtype (fun P : Ideal C => P.IsMaximal ∧ I ≤ P) := ⟨𝔫, inferInstance, hI𝔫⟩
  have hΦ : ∀ y, Φ y 𝔫' = AdicCompletion.semilocalComponent I hI𝔫 y :=
    fun y => AdicCompletion.semilocalComponent_eq I hI𝔫 y
  have hcompat : ∀ x : AdicCompletion (maximalIdeal O) O,
      AdicCompletion.semilocalComponent I hI𝔫 (AdicCompletion.completionBaseChangeHom C (maximalIdeal O) x) =
      algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) x := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal O) n x)
    rw [AdicCompletion.evalₐ_algebraMap_of_liesOver (maximalIdeal O) 𝔫
        (algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C)) n o x ho.symm]
    sorry
  have hrange : ∀ c : AdicCompletion 𝔫 C, algebraMap (AdicCompletion 𝔫 C) F c ∈ ψ.range := by
    intro c
    obtain ⟨y, hy⟩ := Φ.surjective (Function.update 0 𝔫' c)
    obtain ⟨d, hd⟩ := T.surjective y
    have hc : Φ (T d) 𝔫' = c := by rw [hd, hy, Function.update_self]
    suffices h : ∀ d', algebraMap (AdicCompletion 𝔫 C) F (Φ (T d') 𝔫') ∈ ψ.range by
      rw [← hc]; exact h d
    intro d'
    induction d' using TensorProduct.inductionOn with
    | tmul x c₀ =>
      rw [AdicCompletion.tensorRingEquiv_tmul, map_mul, Pi.mul_apply, map_mul]
      refine mul_mem ?_ ?_
      ·
        rw [hΦ, hcompat, ← IsScalarTower.algebraMap_apply (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) F,
          IsScalarTower.algebraMap_apply (AdicCompletion (maximalIdeal O) O) K₀ F]
        exact Subalgebra.algebraMap_mem _ _
      ·
        rw [AdicCompletion.semilocalPiEquiv_of I hI𝔫 c₀]
        have : algebraMap (AdicCompletion 𝔫 C) F (AdicCompletion.of 𝔫 C c₀) =
            ψ (TensorProduct.tmul (FractionRing O) (1 : K₀) (algebraMap C (FractionRing C) c₀)) := by
          rw [hψ, map_one, one_mul, hφC, ← hCĈ]
          rfl
        rw [this]
        exact ⟨_, rfl⟩
    | add x y hx hy =>
      rw [map_add, map_add, Pi.add_apply, map_add]
      exact add_mem hx hy
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨c, s⟩, hz⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid (AdicCompletion 𝔫 C) (nonZeroDivisors (AdicCompletion (maximalIdeal O) O))) z
    obtain ⟨s₀, hs₀, hs₀eq⟩ := Submonoid.mem_map.mp s.2
    have hs₀K : algebraMap (AdicCompletion (maximalIdeal O) O) K₀ s₀ ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs₀
    have hsF : algebraMap (AdicCompletion 𝔫 C) F s =
        algebraMap K₀ F (algebraMap (AdicCompletion (maximalIdeal O) O) K₀ s₀) := by
      rw [← IsScalarTower.algebraMap_apply, ← hs₀eq, ← IsScalarTower.algebraMap_apply]
    have hz' : z = algebraMap (AdicCompletion 𝔫 C) F c *
        algebraMap K₀ F (algebraMap (AdicCompletion (maximalIdeal O) O) K₀ s₀)⁻¹ := by
      rw [← hz, hsF, mul_assoc, ← map_mul, mul_inv_cancel₀ hs₀K, map_one, mul_one]
    exact (AlgHom.mem_range ψ).mp
      (by rw [hz']; exact mul_mem (hrange c) (Subalgebra.algebraMap_mem _ _))

  have : Algebra.FormallyUnramified K₀ (TensorProduct (FractionRing O) K₀ (FractionRing C)) := inferInstance
  have : Module.Finite K₀ (TensorProduct (FractionRing O) K₀ (FractionRing C)) := inferInstance
  have : Algebra.FormallyUnramified K₀ F := Algebra.FormallyUnramified.of_surjective ψ hsurj
  have : Module.Finite K₀ F := Module.Finite.of_surjective ψ.toLinearMap hsurj
  have : Algebra.EssFiniteType K₀ F := inferInstance
  refine ⟨Algebra.FormallyUnramified.isReduced_of_field K₀ F, ?_⟩
  have : Algebra.FormallyEtale K₀ F := Algebra.FormallyEtale.of_formallyUnramified_of_field K₀ F
  obtain ⟨ι, hfin, Ai, _, _, e, hAi⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod K₀ F).mp inferInstance
  have := hfin
  have : Algebra.IsSeparable K₀ (∀ i, Ai i) := BDescN3.isSeparable_pi Ai
  exact AlgEquiv.Algebra.isSeparable e.symm

-- created on 2026-10-09
