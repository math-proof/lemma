import Mathlib
import sympy.Basic
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Module_Flat_finite_free_finrank_quotient_tensorProduct_of_map_maximalIdeal_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_Flat_finite_free_finrank_quotient_tensorProduct_of_map_maximalIdeal_eq.lean)
-/
@[path]
private lemma main
  (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
  (D : Type) [CommRing D] [IsLocalRing D] [Algebra V D] [IsLocalHom (algebraMap V D)] [Module.Flat V D]
  [Module.Finite (ResidueField V) (ResidueField D)]
  (m : ℕ)
  -- given
  (hVD : (maximalIdeal V).map (algebraMap V D) = maximalIdeal D)
  (hm : 0 < m) :
  -- imply
  Module.Finite (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) ∧ Module.Free (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) ∧ Module.finrank (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) = Module.finrank (ResidueField V) (ResidueField D) := by
  -- proof
  classical
  have hItop : maximalIdeal V ^ m ≠ ⊤ := by
    intro h
    have : maximalIdeal V ^ m ≤ maximalIdeal V := Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hm)
    rw [h, top_le_iff] at this
    apply (maximalIdeal.isMaximal V).ne_top this
  let _ : Nontrivial (V ⧸ maximalIdeal V ^ m) := Ideal.Quotient.nontrivial_iff.mpr hItop
  let _ : IsLocalRing (V ⧸ maximalIdeal V ^ m) := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let W := (V ⧸ maximalIdeal V ^ m) ⊗[V] D
  have hfinV : Module.Finite V W := by
    set I : Ideal V := maximalIdeal V with hI
    have hres : Function.Surjective (Algebra.linearMap V (ResidueField V)) := by
      intro y
      obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective y
      exact ⟨v, rfl⟩
    let _ : Module.Finite V (ResidueField V) := Module.Finite.of_surjective (Algebra.linearMap V (ResidueField V)) hres
    let _ : Module.Finite V (ResidueField D) := Module.Finite.trans (ResidueField V) (ResidueField D)
    have hID : (I • ⊤ : Submodule V D) = (maximalIdeal D).restrictScalars V := by
      rw [hI, Ideal.smul_top_eq_map, hVD]
    let ρ : D →ₗ[V] ResidueField D := (Algebra.linearMap D (ResidueField D)).restrictScalars V
    have hρsurj : Function.Surjective ρ := fun y => by obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective y; exact ⟨d, rfl⟩
    have hρker : LinearMap.ker ρ = (I • ⊤ : Submodule V D) := by
      rw [hID]; ext d
      simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem]
      exact IsLocalRing.residue_eq_zero_iff d
    obtain ⟨S₀, hS₀fg, hS₀⟩ : ∃ S₀ : Submodule V D, S₀.FG ∧ S₀ ⊔ (I • ⊤ : Submodule V D) = ⊤ := by
      obtain ⟨t, ht⟩ := Module.finite_def.mp (inferInstance : Module.Finite V (ResidueField D))
      have hlift : ∀ y : ResidueField D, ∃ d : D, ρ d = y := hρsurj
      choose ℓ hℓ using hlift
      refine ⟨Submodule.span V (Finset.image ℓ t : Set D), ⟨_, rfl⟩, ?_⟩
      rw [eq_top_iff]
      intro d _
      have hd : ρ d ∈ Submodule.span V (t : Set (ResidueField D)) := by
        rw [ht]
        apply Submodule.mem_top
      have : Submodule.span V (t : Set (ResidueField D)) = Submodule.map ρ (Submodule.span V (Finset.image ℓ t : Set D)) := by
        rw [Submodule.map_span]; congr 1; ext y; simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
        constructor
        ·
          intro hy
          exact ⟨ℓ y, ⟨y, hy, rfl⟩, hℓ y⟩
        ·
          rintro ⟨d', ⟨y', hy', rfl⟩, rfl⟩
          rw [hℓ]
          apply hy'
      rw [this, Submodule.mem_map] at hd
      obtain ⟨d₀, hd₀, hdd⟩ := hd
      have hdiff : d - d₀ ∈ (I • ⊤ : Submodule V D) := by rw [← hρker, LinearMap.mem_ker, map_sub, hdd, sub_self]
      have : d = d₀ + (d - d₀) := by abel
      rw [this]
      apply Submodule.add_mem_sup hd₀ hdiff
    have hSk : ∀ k : ℕ, S₀ ⊔ (I ^ k • ⊤ : Submodule V D) = ⊤ := by
      intro k
      induction k
      ·
        rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
        apply sup_top_eq _
      ·
        rename_i k ih
        have h1 : (I ^ k • ⊤ : Submodule V D) ≤ S₀ ⊔ (I ^ (k + 1) • ⊤ : Submodule V D) := by
          conv_lhs => rw [← hS₀]
          rw [Submodule.smul_sup, ← Submodule.mul_smul, ← pow_succ]
          apply sup_le_sup_right Submodule.smul_le_right _
        refine eq_top_iff.mpr ?_
        calc
          _ = S₀ ⊔ (I ^ k • ⊤ : Submodule V D) := ih.symm
          _ ≤ S₀ ⊔ (I ^ (k + 1) • ⊤ : Submodule V D) := sup_le le_sup_left h1
    have hfq : Module.Finite V (D ⧸ (I ^ m • ⊤ : Submodule V D)) := by
      rw [Module.finite_def]
      have : (⊤ : Submodule V (D ⧸ (I ^ m • ⊤ : Submodule V D))) = Submodule.map (I ^ m • ⊤ : Submodule V D).mkQ S₀ := by
        have htop : Submodule.map (I ^ m • ⊤ : Submodule V D).mkQ ⊤ = ⊤ := by
          rw [Submodule.map_top, Submodule.range_mkQ]
        have h := congrArg (Submodule.map (I ^ m • ⊤ : Submodule V D).mkQ) (hSk m)
        rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq, htop] at h
        apply h.symm
      rw [this]
      apply hS₀fg.map _
    apply Module.Finite.equiv (TensorProduct.quotTensorEquivQuotSMul D (I ^ m)).symm
  let _ : Module.Finite (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) := Module.Finite.of_restrictScalars_finite V (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D)
  let _ : Module.Free (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) := Module.free_of_flat_of_isLocalRing
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hle : maximalIdeal V ^ m ≤ maximalIdeal V := Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hm)
  let algK : Algebra (V ⧸ maximalIdeal V ^ m) (ResidueField V) := (Ideal.Quotient.factor hle).toAlgebra
  let _ : IsScalarTower V (V ⧸ maximalIdeal V ^ m) (ResidueField V) := IsScalarTower.of_algebraMap_eq (fun v => rfl)
  have hb1 : Module.finrank (ResidueField V) ((ResidueField V) ⊗[(V ⧸ maximalIdeal V ^ m)] ((V ⧸ maximalIdeal V ^ m) ⊗[V] D)) = Module.finrank (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul]
  let e2 : ((ResidueField V) ⊗[(V ⧸ maximalIdeal V ^ m)] ((V ⧸ maximalIdeal V ^ m) ⊗[V] D)) ≃ₗ[(ResidueField V)] ((ResidueField V) ⊗[V] D) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange V (V ⧸ maximalIdeal V ^ m) (ResidueField V) (ResidueField V) D
  let φ : ((ResidueField V) ⊗[V] D) →ₐ[(ResidueField V)] (ResidueField D) :=
    Algebra.TensorProduct.lift (Algebra.ofId (ResidueField V) (ResidueField D)) (IsScalarTower.toAlgHom V D (ResidueField D)) (fun x y => Commute.all _ _)
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective y
    refine ⟨(1 : ResidueField V) ⊗ₜ[V] d, ?_⟩
    show φ ((1 : ResidueField V) ⊗ₜ[V] d) = residue D d
    rw [Algebra.TensorProduct.lift_tmul]
    simp
  have hker : (maximalIdeal D) ≤ RingHom.ker ((Algebra.TensorProduct.includeRight : D →ₐ[V] (ResidueField V) ⊗[V] D).toRingHom) := by
    rw [← hVD, Ideal.map_le_iff_le_comap]
    intro v hv
    show ((1 : ResidueField V) ⊗ₜ[V] (algebraMap V D v) : (ResidueField V) ⊗[V] D) = 0
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    rw [show algebraMap V (ResidueField V) v = 0 from (IsLocalRing.residue_eq_zero_iff v).mpr hv, TensorProduct.zero_tmul]
  let ψ : (ResidueField D) →+* ((ResidueField V) ⊗[V] D) := Ideal.Quotient.lift (maximalIdeal D)
    ((Algebra.TensorProduct.includeRight : D →ₐ[V] (ResidueField V) ⊗[V] D).toRingHom) (fun a ha => hker ha)
  have hψφ : ∀ z, ψ (φ z) = z := by
    intro z
    refine TensorProduct.inductionOn z ?_ ?_
    ·
      intro k d
      obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective k
      rw [Algebra.TensorProduct.lift_tmul]
      show ψ ((Algebra.ofId (ResidueField V) (ResidueField D)) (residue V v) * residue D d) = residue V v ⊗ₜ[V] d
      have h1 : (Algebra.ofId (ResidueField V) (ResidueField D)) (residue V v) * residue D d = residue D (algebraMap V D v * d) := by
        rw [map_mul]; congr 1
      rw [h1]
      show (Ideal.Quotient.lift (maximalIdeal D) _ _) (Ideal.Quotient.mk (maximalIdeal D) (algebraMap V D v * d)) = _
      rw [Ideal.Quotient.lift_mk]
      show ((1 : ResidueField V) ⊗ₜ[V] (algebraMap V D v * d) : (ResidueField V) ⊗[V] D) = residue V v ⊗ₜ[V] d
      rw [← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
      rfl
    ·
      intro x y hx hy
      rw [map_add, map_add, hx, hy]
  have hφinj : Function.Injective φ := fun a b h => by rw [← hψφ a, ← hψφ b, h]
  let e3 : ((ResidueField V) ⊗[V] D) ≃ₗ[(ResidueField V)] (ResidueField D) := LinearEquiv.ofBijective φ.toLinearMap ⟨hφinj, hφsurj⟩
  rw [← hb1, LinearEquiv.finrank_eq (e2.trans e3)]


-- created on 2026-10-20
