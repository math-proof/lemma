import Mathlib
import sympy.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w

private lemma VAAux.span_pair_eq_span_singleton (V : Type v) [CommRing V] [IsDomain V] [ValuationRing V] (L : Type v) [Field L] [Algebra V L] [IsFractionRing V L] (a g : L) : ∃ h : L, Submodule.span V {a, g} = Submodule.span V {h} := by
  classical
  obtain ⟨x, d, hd, hx⟩ := IsFractionRing.div_surjective (A := V) a
  obtain ⟨y, d', hd', hy⟩ := IsFractionRing.div_surjective (A := V) g
  have hd0 : algebraMap V L d ≠ 0 := IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors L le_rfl hd
  have hd'0 : algebraMap V L d' ≠ 0 := IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors L le_rfl hd'
  obtain ⟨c, hc⟩ | ⟨c, hc⟩ := ValuationRing.dvd_total (x * d') (y * d)
  ·
    refine ⟨a, ?_⟩
    have hg : g = c • a := by
      rw [← hx, ← hy, Algebra.smul_def]
      field_simp [hd0, hd'0]
      have := congrArg (algebraMap V L) hc
      simp only [map_mul] at this
      linear_combination this
    rw [hg]
    apply le_antisymm
    ·
      rw [Submodule.span_le]
      intro z hz
      obtain rfl | rfl := hz
      · exact Submodule.subset_span rfl
      · exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  ·
    refine ⟨g, ?_⟩
    have ha : a = c • g := by
      rw [← hx, ← hy, Algebra.smul_def]
      field_simp [hd0, hd'0]
      have := congrArg (algebraMap V L) hc
      simp only [map_mul] at this
      linear_combination this
    rw [ha]
    apply le_antisymm
    ·
      rw [Submodule.span_le]
      intro z hz
      obtain rfl | rfl := hz
      · exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      · exact Submodule.subset_span rfl
    · exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl))
private lemma VAAux.exists_span_eq_span_singleton (V : Type v) [CommRing V] [IsDomain V] [ValuationRing V] (L : Type v) [Field L] [Algebra V L] [IsFractionRing V L] (s : Finset L) : ∃ g : L, Submodule.span V (s : Set L) = Submodule.span V {g} := by
  classical
  refine Finset.induction_on s ?_ ?_
  · exact ⟨0, by simp⟩
  ·
    intro a s _ ih
    obtain ⟨g, hg⟩ := ih
    obtain ⟨h, hh⟩ := VAAux.span_pair_eq_span_singleton V L a g
    refine ⟨h, ?_⟩
    rw [Finset.coe_insert, Submodule.span_insert, hg, ← Submodule.span_insert, hh]
/--
[Module_Invertible_quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_Invertible_quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing.lean)
-/
@[path]
private lemma main
  {𝒪 : Type u} [CommRing 𝒪]
  (V : Type v) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra 𝒪 V]
  (L : Type v) [Field L] [Algebra 𝒪 L] [Algebra V L] [IsScalarTower 𝒪 V L] [IsFractionRing V L]
  (M : Type w) [AddCommGroup M] [Module 𝒪 M] [Module.Finite 𝒪 M]
  (N : Submodule L (L ⊗[𝒪] M))
  -- given
  (hN : Module.Invertible L ((L ⊗[𝒪] M) ⧸ N)) :
  -- imply
  Module.Invertible V ((V ⊗[𝒪] M) ⧸ Submodule.span V {x : V ⊗[𝒪] M | LinearMap.rTensor M (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ N}) ∧ Submodule.span L (LinearMap.rTensor M (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap '' (Submodule.span V {x : V ⊗[𝒪] M | LinearMap.rTensor M (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ N} : Set (V ⊗[𝒪] M))) = N := by
  -- proof
  classical
  set φ : V ⊗[𝒪] M →ₗ[𝒪] L ⊗[𝒪] M := LinearMap.rTensor M (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap with hφ
  set S : Set (V ⊗[𝒪] M) := {x : V ⊗[𝒪] M | φ x ∈ N} with hS
  let e : L ⊗[V] (V ⊗[𝒪] M) ≃ₗ[L] L ⊗[𝒪] M := TensorProduct.AlgebraTensorModule.cancelBaseChange 𝒪 V L L M
  let ι : V ⊗[𝒪] M →ₗ[V] L ⊗[V] (V ⊗[𝒪] M) := TensorProduct.mk V L (V ⊗[𝒪] M) 1
  let φV : V ⊗[𝒪] M →ₗ[V] L ⊗[𝒪] M := LinearMap.comp ((e.restrictScalars V).toLinearMap) ι
  have hφV : ∀ x, φV x = φ x := by
    intro x
    show e (1 ⊗ₜ[V] x) = φ x
    refine TensorProduct.inductionOn x ?_ ?_
    ·
      intro a m
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, hφ, LinearMap.rTensor_tmul]
      simp [Algebra.smul_def]
    ·
      intro x y hx hy
      rw [TensorProduct.tmul_add, map_add, hx, hy, map_add]
  let N₀ : Submodule V (V ⊗[𝒪] M) := (N.restrictScalars V).comap φV
  have hN₀S : (N₀ : Set (V ⊗[𝒪] M)) = S := by
    ext x
    simp [N₀, hS, hφV]
  have hspanS : Submodule.span V S = N₀ := by rw [← hN₀S, Submodule.span_eq]
  rw [hspanS]
  let _ : IsLocalizedModule (nonZeroDivisors V) ι := inferInstance
  constructor
  ·
    let _ : Module.Free L ((L ⊗[𝒪] M) ⧸ N) := Module.Free.of_divisionRing L _
    have hfr : Module.finrank L ((L ⊗[𝒪] M) ⧸ N) = 1 := Module.Invertible.finrank_eq_one L _
    have hpos : 0 < Module.finrank L ((L ⊗[𝒪] M) ⧸ N) := by
      rw [hfr]
      apply one_pos
    let _ : Module.Finite L ((L ⊗[𝒪] M) ⧸ N) := Module.finite_of_finrank_pos hpos
    let eQ : ((L ⊗[𝒪] M) ⧸ N) ≃ₗ[L] L := LinearEquiv.ofFinrankEq _ _ (by rw [hfr, Module.finrank_self])
    let ψ : V ⊗[𝒪] M →ₗ[V] L := LinearMap.comp ((eQ.restrictScalars V).toLinearMap) (LinearMap.comp ((N.mkQ).restrictScalars V) φV)
    have hψ : ∀ x, ψ x = eQ (N.mkQ (φV x)) := fun _ => rfl
    have hkerψ : LinearMap.ker ψ = N₀ := by
      ext x
      rw [LinearMap.mem_ker, hψ, map_eq_zero_iff _ eQ.injective, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      rfl
    let I : Submodule V L := LinearMap.range ψ
    have eI : ((V ⊗[𝒪] M) ⧸ N₀) ≃ₗ[V] ↥I := (Submodule.quotEquivOfEq _ _ hkerψ.symm).trans ψ.quotKerEquivRange
    let _ : Module.Finite V (V ⊗[𝒪] M) := inferInstance
    have hIfg : I.FG := Module.Finite.iff_fg.mp inferInstance
    obtain ⟨t, ht⟩ := hIfg
    obtain ⟨g, hg⟩ := VAAux.exists_span_eq_span_singleton V L t
    have hIg : I = Submodule.span V {g} := by rw [← ht, hg]
    have hg0 : g ≠ 0 := by
      intro hg0
      have hI0 : I = ⊥ := by rw [hIg, hg0, Submodule.span_singleton_eq_bot]
      have hφN : ∀ p : V ⊗[𝒪] M, φ p ∈ N := by
        intro p
        have : ψ p ∈ I := LinearMap.mem_range_self ψ p
        rw [hI0, Submodule.mem_bot, hψ, map_eq_zero_iff _ eQ.injective, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hφV] at this
        apply this
      have hNtop : N = ⊤ := by
        rw [eq_top_iff]
        intro n _
        obtain ⟨⟨p, s⟩, hps⟩ := IsLocalizedModule.surj (nonZeroDivisors V) ι (e.symm n)
        have hs0 : (algebraMap V L s) ≠ 0 := IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors L le_rfl s.2
        have h1 : algebraMap V L s • n = φ p := by
          have := congrArg e hps
          simp only [Submonoid.smul_def] at this
          rw [← algebraMap_smul (A := L), map_smul, LinearEquiv.apply_symm_apply] at this
          rw [← hφV]
          apply this
        have : n = (algebraMap V L s)⁻¹ • φ p := by rw [← h1, smul_smul, inv_mul_cancel₀ hs0, one_smul]
        rw [this]
        apply N.smul_mem _ (hφN p)
      let _ : Subsingleton ((L ⊗[𝒪] M) ⧸ N) := Submodule.Quotient.subsingleton_iff.mpr hNtop
      have := Module.finrank_zero_of_subsingleton (R := L) (M := (L ⊗[𝒪] M) ⧸ N)
      rw [hfr] at this
      apply one_ne_zero this
    refine Module.Invertible.congr (eI.trans ((LinearEquiv.ofEq _ _ hIg).trans (LinearEquiv.toSpanNonzeroSingleton V L g hg0).symm)).symm
  ·
    apply le_antisymm
    ·
      rw [Submodule.span_le]
      intro _ hx
      obtain ⟨x, hx, rfl⟩ := hx
      have : φV x ∈ N := hx
      rwa [hφV] at this
    ·
      intro n hn
      obtain ⟨⟨p, s⟩, hps⟩ := IsLocalizedModule.surj (nonZeroDivisors V) ι (e.symm n)
      have hs0 : (algebraMap V L s) ≠ 0 := IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors L le_rfl s.2
      have h1 : algebraMap V L s • n = φ p := by
        have := congrArg e hps
        simp only [Submonoid.smul_def] at this
        rw [← algebraMap_smul (A := L), map_smul, LinearEquiv.apply_symm_apply] at this
        rw [← hφV]
        apply this
      have hpS : p ∈ N₀ := by
        show φV p ∈ N
        rw [hφV, ← h1]
        apply N.smul_mem _ hn
      have : n = (algebraMap V L s)⁻¹ • φ p := by rw [← h1, smul_smul, inv_mul_cancel₀ hs0, one_smul]
      rw [this]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, hpS, rfl⟩)


-- created on 2026-10-20
