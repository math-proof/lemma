import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private def IsSaturated {𝒪 : Type} [CommRing 𝒪] {M : Type} [AddCommGroup M] [Module 𝒪 M] (A : Submodule 𝒪 M) : Prop := ∀ (a : 𝒪), a ≠ 0 → ∀ m : M, a • m ∈ A → m ∈ A
private lemma eq_zero_of_forall_pow_dvd {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {ϖ c : 𝒪} (hϖ : Irreducible ϖ) (h : ∀ n : ℕ, ϖ ^ n ∣ c) : c = 0 := by
  by_contra hc
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  have hle : IsDiscreteValuationRing.addVal 𝒪 (ϖ ^ (m + 1)) ≤ IsDiscreteValuationRing.addVal 𝒪 ((u : 𝒪) * ϖ ^ m) := IsDiscreteValuationRing.addVal_le_iff_dvd.mpr (h (m + 1))
  rw [hϖ.addVal_pow, IsDiscreteValuationRing.addVal_def' u hϖ m] at hle
  have : (m + 1 : ℕ) ≤ m := by
    exact_mod_cast hle
  omega
private lemma eq_zero_of_forall_exists_pow_smul {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {M : Type} [AddCommGroup M] [Module 𝒪 M] [Module.Free 𝒪 M] {ϖ : 𝒪} {v : M} (hϖ : Irreducible ϖ) (h : ∀ n : ℕ, ∃ w : M, v = ϖ ^ n • w) : v = 0 := by
  classical
  set b := Module.Free.chooseBasis 𝒪 M
  refine b.ext_elem fun j => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine eq_zero_of_forall_pow_dvd hϖ fun n => ?_
  obtain ⟨w, hw⟩ := h n
  refine ⟨b.repr w j, ?_⟩
  rw [hw, map_smul, Finsupp.smul_apply, smul_eq_mul]
private lemma injective_of_residual {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {M : Type} [AddCommGroup M] [Module 𝒪 M] [Module.Free 𝒪 M] {M' : Type} [AddCommGroup M'] [Module 𝒪 M'] [Module.Free 𝒪 M'] {i : M →ₗ[𝒪] M'} {ϖ : 𝒪} (hϖ : Irreducible ϖ) (hres : ∀ (v : M) (x : M'), i v = ϖ • x → ∃ v₁ : M, v = ϖ • v₁) : Function.Injective i := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  refine eq_zero_of_forall_exists_pow_smul hϖ fun n => ?_
  induction n
  · refine ⟨v, by rw [pow_zero, one_smul]⟩
  ·
    rename_i n ih
    obtain ⟨w, rfl⟩ := ih
    have hiw : i w = 0 := by
      apply (smul_eq_zero.mp (by rw [← map_smul, hv])).resolve_left (pow_ne_zero n hϖ.ne_zero)
    obtain ⟨w₁, rfl⟩ := hres w 0 (by rw [hiw, smul_zero])
    refine ⟨w₁, ?_⟩
    rw [pow_succ, mul_smul]
private lemma isSaturated_of_uniformizer {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {M : Type} [AddCommGroup M] [Module 𝒪 M] {A : Submodule 𝒪 M} {ϖ : 𝒪} (hϖ : Irreducible ϖ) (h : ∀ m : M, ϖ • m ∈ A → m ∈ A) : IsSaturated A := by
  intro a ha m ham
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hn : ϖ ^ n • m ∈ A := by
    have := A.smul_mem (↑u⁻¹ : 𝒪) ham
    rwa [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
  clear ham ha
  induction n generalizing m
  ·
    simp at hn
    apply hn
  ·
    rename_i n ih
    apply ih
    apply h
    rwa [smul_smul, ← pow_succ']
private lemma isSaturated_map {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {M : Type} [AddCommGroup M] [Module 𝒪 M] {M' : Type} [AddCommGroup M'] [Module 𝒪 M'] [Module.Free 𝒪 M'] {i : M →ₗ[𝒪] M'} {ϖ : 𝒪} {A : Submodule 𝒪 M} (hϖ : Irreducible ϖ) (hres : ∀ (v : M) (x : M'), i v = ϖ • x → ∃ v₁ : M, v = ϖ • v₁) (hA : IsSaturated A) : IsSaturated (A.map i) := by
  refine isSaturated_of_uniformizer hϖ fun y hy => ?_
  obtain ⟨x, hxA, hxy⟩ := Submodule.mem_map.mp hy
  obtain ⟨x₁, rfl⟩ := hres x y hxy
  have hx₁ : x₁ ∈ A := hA ϖ hϖ.ne_zero x₁ hxA
  refine Submodule.mem_map.mpr ⟨x₁, hx₁, ?_⟩
  exact smul_right_injective M' hϖ.ne_zero (by rw [← map_smul, hxy])
private lemma eq_of_le_of_finrank_le_of_isSaturated {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {M' : Type} [AddCommGroup M'] [Module 𝒪 M'] [Module.Finite 𝒪 M'] {W B : Submodule 𝒪 M'} (hWB : W ≤ B) (hrk : Module.finrank 𝒪 B ≤ Module.finrank 𝒪 W) (hW : IsSaturated W) : W = B := by
  classical
  let _ : IsNoetherianRing 𝒪 := inferInstance
  let _ : IsNoetherian 𝒪 M' := isNoetherian_of_isNoetherianRing_of_finite 𝒪 M'
  refine le_antisymm hWB fun y hy => ?_
  set W' : Submodule 𝒪 B := W.comap B.subtype with hW'
  have hmap : W'.map B.subtype = W := by
    rw [hW', Submodule.map_comap_subtype, inf_eq_right.mpr hWB]
  have hfinW' : Module.finrank 𝒪 W' = Module.finrank 𝒪 W := by
    rw [← Submodule.finrank_map_subtype_eq B W', hmap]
  have hq : Module.finrank 𝒪 (B ⧸ W') = 0 := by
    have h := Submodule.finrank_quotient_add_finrank W'
    omega
  have htor : Module.IsTorsion 𝒪 (B ⧸ W') := (Module.finrank_eq_zero_iff_isTorsion).mp hq
  obtain ⟨⟨a, ha⟩, hay⟩ := @htor (Submodule.Quotient.mk ⟨y, hy⟩)
  have ha0 : (a : 𝒪) ≠ 0 := nonZeroDivisors.ne_zero ha
  have hmem : a • (⟨y, hy⟩ : B) ∈ W' := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    apply hay
  simpa using hW a ha0 y (Submodule.mem_comap.mp hmem)
/--
[IharaTower_map_torsionBySet_eq_of_forall_eq_smul_of_finrank_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IharaTower_map_torsionBySet_eq_of_forall_eq_smul_of_finrank_le.lean)
-/
@[path]
private lemma main
  {𝒪 T T' M M' : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [CommRing T] [Algebra 𝒪 T] [CommRing T'] [Algebra 𝒪 T'] [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M] [Module.Finite 𝒪 M] [Module.Free 𝒪 M] [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M'] [Module.Finite 𝒪 M'] [Module.Free 𝒪 M']
  {i : M →ₗ[𝒪] M'} {πT : T →ₐ[𝒪] 𝒪} {πT' : T' →ₐ[𝒪] 𝒪} {ϖ : 𝒪}
  (hϖ : Irreducible ϖ)
  (hres : ∀ (v : M) (x : M'), i v = ϖ • x → ∃ v₁ : M, v = ϖ • v₁)
  (hincl : Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) ≤ (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪)
  (hrank : Module.finrank 𝒪 ((Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪) ≤ Module.finrank 𝒪 ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪)) :
  -- imply
  Function.Injective i ∧ Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) = (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪 := by
  -- proof
  classical
  have hinj : Function.Injective i := injective_of_residual (i := i) hϖ hres
  refine ⟨hinj, ?_⟩
  set A : Submodule 𝒪 M := (Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪 with hAdef
  set B : Submodule 𝒪 M' := (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪
  have hAsat : IsSaturated A := by
    intro a ha m ham
    rw [hAdef, Submodule.restrictScalars_mem, Submodule.mem_torsionBySet_iff] at ham ⊢
    intro t
    apply (smul_eq_zero.mp (by rw [smul_comm, ham t])).resolve_left ha
  refine eq_of_le_of_finrank_le_of_isSaturated (W := A.map i) (B := B) hincl ?_ (isSaturated_map (i := i) (A := A) hϖ hres hAsat)
  rwa [(Submodule.equivMapOfInjective i hinj A).symm.finrank_eq]


-- created on 2026-10-20
