import Mathlib
import sympy.Basic

open Module

/--
[AddSubgroup_exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddSubgroup_exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology.lean)
-/

private lemma  exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {L : AddSubgroup V} [hL : DiscreteTopology L] :
  ∃ (a b : ℕ) (T : ((Fin a → ℝ) × (Fin b → ℝ)) ≃L[ℝ] V),
    ∀ x : V, x ∈ L ↔ ∃ k : Fin a → ℤ, T (fun i => (k i : ℝ), 0) = x := by
  classical

  set L₁ : Submodule ℤ V := AddSubgroup.toIntSubmodule L with hL₁
  have hmemL₁ : ∀ x, x ∈ L₁ ↔ x ∈ L := fun x => Iff.rfl
  have : DiscreteTopology L₁ := hL

  set W : Submodule ℝ V := Submodule.span ℝ (L₁ : Set V) with hW
  set L₂ : Submodule ℤ W := ZLattice.comap ℝ L₁ W.subtype with hL₂
  have hmemL₂ : ∀ x : W, x ∈ L₂ ↔ (x : V) ∈ L := by
    intro x
    rw [hL₂, ← SetLike.mem_coe, ZLattice.coe_comap]
    rfl
  have hdisc : DiscreteTopology L₂ :=
    ZLattice.comap_discreteTopology ℝ L₁ (by fun_prop) Subtype.val_injective
  have hlat : IsZLattice ℝ L₂ := by
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective W.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    apply le_antisymm
    ·
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      exact Submodule.subset_span ((hmemL₂ x).mp hx)
    ·
      have hsub : (L₁ : Set V) ⊆ ⇑W.subtype '' (L₂ : Set W) := by
        intro v hv
        exact ⟨⟨v, Submodule.subset_span hv⟩, (hmemL₂ _).mpr hv, rfl⟩
      intro v hv
      exact Submodule.span_mono hsub hv
  have : Module.Free ℤ L₂ := ZLattice.module_free ℝ L₂
  have : Module.Finite ℤ L₂ := ZLattice.module_finite ℝ L₂
  set a : ℕ := Module.finrank ℤ L₂ with ha
  set bZ : Basis (Fin a) ℤ L₂ := Module.finBasis ℤ L₂ with hbZ
  set BW : Basis (Fin a) ℝ W := Basis.ofZLatticeBasis ℝ L₂ bZ with hBW
  have hBW : ∀ i, BW i = (bZ i : W) := fun i => Basis.ofZLatticeBasis_apply ℝ L₂ bZ i

  obtain ⟨W', hWW'⟩ := Submodule.exists_isCompl W
  set b : ℕ := Module.finrank ℝ W' with hb
  set BW' : Basis (Fin b) ℝ W' := Module.finBasis ℝ W' with hBW'

  set e₁ : LinearEquiv (RingHom.id ℝ) ((Fin a → ℝ) × (Fin b → ℝ)) (W × W') :=
    LinearEquiv.prodCongr BW.equivFun.symm BW'.equivFun.symm with he₁
  set e₂ : LinearEquiv (RingHom.id ℝ) (W × W') V := Submodule.prodEquivOfIsCompl W W' hWW' with he₂
  set T : ((Fin a → ℝ) × (Fin b → ℝ)) ≃L[ℝ] V := (e₁.trans e₂).toContinuousLinearEquiv with hT
  have hTapply : ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
      T (w, z) = ((BW.equivFun.symm w : W) : V) + ((BW'.equivFun.symm z : W') : V) := by
    intro w z
    rfl
  have hT0 : ∀ k : Fin a → ℤ, T ((fun i => (k i : ℝ)), 0) = ∑ i, (k i) • ((bZ i : W) : V) := by
    intro k
    rw [hTapply, map_zero, ZeroMemClass.coe_zero, add_zero, Basis.equivFun_symm_apply,
      Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, hBW, Int.cast_smul_eq_zsmul]
  refine ⟨a, b, T, fun x => ⟨fun hx => ?_, ?_⟩⟩
  ·
    have hxW : x ∈ W := Submodule.subset_span ((hmemL₁ x).mpr hx)
    have hxL₂ : (⟨x, hxW⟩ : W) ∈ L₂ := (hmemL₂ _).mpr hx
    set k : Fin a → ℤ := bZ.equivFun ⟨⟨x, hxW⟩, hxL₂⟩ with hk
    refine ⟨k, ?_⟩
    rw [hT0]
    have h := bZ.sum_equivFun ⟨⟨x, hxW⟩, hxL₂⟩
    have h' := congrArg (fun z : L₂ => ((z : W) : V)) h
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h'
    exact h'
  ·
    rintro ⟨k, rfl⟩
    rw [hT0]
    apply L.sum_mem
    intro i _
    apply L.zsmul_mem
    exact (hmemL₂ _).mp (bZ i).2
@[main]
private lemma main
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {L : AddSubgroup V} [DiscreteTopology L] :
-- imply
  ∃ (a b : ℕ) (T : ((Fin a → ℝ) × (Fin b → ℝ)) ≃L[ℝ] V),
      ∀ x : V, x ∈ L ↔ ∃ k : Fin a → ℤ, T (fun i => (k i : ℝ), 0) = x :=
-- proof
  exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology (L := L)


-- created on 2026-10-09
