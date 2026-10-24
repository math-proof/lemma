import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

section

variable {k : Type u} [Field k] {C : Type v} [AddCommGroup C] [Module k C]
private noncomputable def cR (ψ : Module.Dual k C) : C ⊗[k] C →ₗ[k] C :=
  LinearMap.comp (TensorProduct.rid k C).toLinearMap (LinearMap.lTensor C ψ)
@[simp] private lemma cR_tmul (ψ : Module.Dual k C) (a b : C) : cR ψ (a ⊗ₜ[k] b) = ψ b • a := by
  simp [cR]
private noncomputable def cL (φ : Module.Dual k C) : C ⊗[k] C →ₗ[k] C :=
  LinearMap.comp (TensorProduct.lid k C).toLinearMap (LinearMap.rTensor C φ)
@[simp] private lemma cL_tmul (φ : Module.Dual k C) (a b : C) : cL φ (a ⊗ₜ[k] b) = φ a • b := by
  simp [cL]
private lemma lTensor_cR_assoc (ψ : Module.Dual k C) (z : C ⊗[k] C) (r : C) :
  LinearMap.lTensor C (cR ψ) (TensorProduct.assoc k C C C (z ⊗ₜ[k] r)) = ψ r • z := by
  refine TensorProduct.inductionOn z ?_ ?_
  ·
    intro p q
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  ·
    intro z₁ z₂ h₁ h₂
    simp only [TensorProduct.add_tmul, map_add, h₁, h₂, smul_add]
private lemma rTensor_cL_assoc_symm (φ : Module.Dual k C) (p : C) (z : C ⊗[k] C) :
  LinearMap.rTensor C (cL φ) ((TensorProduct.assoc k C C C).symm (p ⊗ₜ[k] z)) = φ p • z := by
  refine TensorProduct.inductionOn z ?_ ?_
  ·
    intro q r
    simp [TensorProduct.smul_tmul']
  ·
    intro z₁ z₂ h₁ h₂
    simp only [TensorProduct.tmul_add, map_add, h₁, h₂, smul_add]
private lemma exists_dual_family {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → C) (he : LinearIndependent k e) :
  ∃ ψ : ι → Module.Dual k C, ∀ i j, ψ i (e j) = if i = j then 1 else 0 := by
  classical
  let b := Module.Basis.span he
  have hb : ∀ j, (b j : C) = e j := fun j => congrArg Subtype.val (Module.Basis.span_apply he j)
  have hext : ∀ i, ∃ g : C →ₗ[k] k, LinearMap.comp g (Submodule.span k (Set.range e)).subtype = b.coord i := fun i =>
    LinearMap.exists_extend (b.coord i)
  choose ψ hψ using hext
  refine ⟨ψ, fun i j => ?_⟩
  have : ψ i (b j : C) = b.coord i (b j) := by
    rw [← hψ i]; rfl
  rw [← hb, this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp [eq_comm]
private lemma eq_sum_cR_tmul {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → C) (ψ : ι → Module.Dual k C) (hψ : ∀ i j, ψ i (e j) = if i = j then 1 else 0) (A : Submodule k C) (t : C ⊗[k] C) (ht : t ∈ Submodule.span k {s : C ⊗[k] C | ∃ a ∈ A, ∃ b ∈ Submodule.span k (Set.range e), s = a ⊗ₜ[k] b}) :
  t = ∑ l, cR (ψ l) t ⊗ₜ[k] e l := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ht
  ·
    intro s hs
    obtain ⟨a, -, b, hb, rfl⟩ := hs
    have hbexp : b = ∑ l, ψ l b • e l := by
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
      ·
        intro c hc
        obtain ⟨j, rfl⟩ := hc
        rw [Finset.sum_eq_single j]
        · rw [hψ, ite_eq_left rfl, one_smul]
        ·
          intro l _ hlj
          rw [hψ, ite_eq_right hlj, zero_smul]
        ·
          intro h
          apply absurd (Finset.mem_univ j) h
      · simp
      ·
        intro c d _ _ hc hd
        conv_lhs => rw [hc, hd]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [map_add, add_smul]
      ·
        intro r c _ hc
        conv_lhs => rw [hc]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [map_smul, smul_eq_mul, mul_smul]
    conv_lhs => rw [hbexp]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [cR_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  · simp
  ·
    intro s t _ _ hs ht
    conv_lhs => rw [hs, ht]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_add, TensorProduct.add_tmul]
  ·
    intro r s _ hs
    conv_lhs => rw [hs]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, TensorProduct.smul_tmul']
private lemma eq_sum_tmul_cL {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → C) (φ : ι → Module.Dual k C) (hφ : ∀ i j, φ i (u j) = if i = j then 1 else 0) (B : Submodule k C) (t : C ⊗[k] C) (ht : t ∈ Submodule.span k {s : C ⊗[k] C | ∃ a ∈ Submodule.span k (Set.range u), ∃ b ∈ B, s = a ⊗ₜ[k] b}) :
  t = ∑ j, u j ⊗ₜ[k] cL (φ j) t := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ht
  ·
    intro s hs
    obtain ⟨a, ha, b, -, rfl⟩ := hs
    have haexp : a = ∑ j, φ j a • u j := by
      refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
      ·
        intro c hc
        obtain ⟨j, rfl⟩ := hc
        rw [Finset.sum_eq_single j]
        · rw [hφ, ite_eq_left rfl, one_smul]
        ·
          intro l _ hlj
          rw [hφ, ite_eq_right hlj, zero_smul]
        ·
          intro h
          apply absurd (Finset.mem_univ j) h
      · simp
      ·
        intro c d _ _ hc hd
        conv_lhs => rw [hc, hd]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [map_add, add_smul]
      ·
        intro r c _ hc
        conv_lhs => rw [hc]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [map_smul, smul_eq_mul, mul_smul]
    conv_lhs => rw [haexp]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cL_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  · simp
  ·
    intro s t _ _ hs ht
    conv_lhs => rw [hs, ht]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_add, TensorProduct.tmul_add]
  ·
    intro r s _ hs
    conv_lhs => rw [hs]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, TensorProduct.tmul_smul]
private lemma cR_mem (ψ : Module.Dual k C) (A B : Submodule k C) (t : C ⊗[k] C) (ht : t ∈ Submodule.span k {s : C ⊗[k] C | ∃ a ∈ A, ∃ b ∈ B, s = a ⊗ₜ[k] b}) : cR ψ t ∈ A := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ht
  ·
    intro s hs
    obtain ⟨a, ha, b, -, rfl⟩ := hs
    rw [cR_tmul]
    apply A.smul_mem _ ha
  ·
    rw [map_zero]
    apply A.zero_mem
  ·
    intro s t _ _ hs ht
    rw [map_add]
    apply A.add_mem hs ht
  ·
    intro r s _ hs
    rw [map_smul]
    apply A.smul_mem _ hs
private lemma cL_mem (φ : Module.Dual k C) (A B : Submodule k C) (t : C ⊗[k] C) (ht : t ∈ Submodule.span k {s : C ⊗[k] C | ∃ a ∈ A, ∃ b ∈ B, s = a ⊗ₜ[k] b}) : cL φ t ∈ B := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ht
  ·
    intro s hs
    obtain ⟨a, -, b, hb, rfl⟩ := hs
    rw [cL_tmul]
    apply B.smul_mem _ hb
  ·
    rw [map_zero]
    apply B.zero_mem
  ·
    intro s t _ _ hs ht
    rw [map_add]
    apply B.add_mem hs ht
  ·
    intro r s _ hs
    rw [map_smul]
    apply B.smul_mem _ hs
private lemma span_tmul_mono {A A' B B' : Submodule k C} (hA : A ≤ A') (hB : B ≤ B') :
  Submodule.span k {s : C ⊗[k] C | ∃ a ∈ A, ∃ b ∈ B, s = a ⊗ₜ[k] b}
    ≤ Submodule.span k {s : C ⊗[k] C | ∃ a ∈ A', ∃ b ∈ B', s = a ⊗ₜ[k] b} :=
  Submodule.span_mono fun _ ⟨a, ha, b, hb, hs⟩ => ⟨a, hA ha, b, hB hb, hs⟩
private lemma tmul_mem_span {A B : Submodule k C} {a b : C} (ha : a ∈ A) (hb : b ∈ B) :
  a ⊗ₜ[k] b ∈ Submodule.span k {s : C ⊗[k] C | ∃ a ∈ A, ∃ b ∈ B, s = a ⊗ₜ[k] b} :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩
end

/--
[Coalgebra_exists_finiteDimensional_le_comul_mem_span](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Coalgebra_exists_finiteDimensional_le_comul_mem_span.lean)
-/
@[path]
private lemma main
  {k : Type u} {C : Type v} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]
    (K : Submodule k C)
    (hK : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : C ⊗[k] C | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (x : C) (hx : x ∈ K) :
    -- imply
    ∃ D : Submodule k C, D ≤ K ∧ FiniteDimensional k ↥D ∧ x ∈ D ∧
      ∀ y ∈ D, Coalgebra.comul (R := k) y ∈
        Submodule.span k {t : C ⊗[k] C | ∃ a ∈ D, ∃ b ∈ D, t = a ⊗ₜ[k] b} := by
  -- proof
  classical
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.mp (hK x hx)
  choose a ha b hb hab using (fun i => (g i).2)
  obtain ⟨t, ht_sub, ht_span, ht_li⟩ := exists_linearIndependent k (Set.range b)
  have ht_fin : t.Finite := (Set.finite_range b).subset ht_sub
  let _ : Fintype ↥t := ht_fin.fintype
  let e : ↥t → C := Subtype.val
  obtain ⟨ψ, hψ⟩ := exists_dual_family e ht_li
  have hrange_e : Set.range e = t := Subtype.range_coe
  have hb_mem : ∀ i, b i ∈ Submodule.span k (Set.range e) := fun i => by
    rw [hrange_e, ht_span]; apply Submodule.subset_span (Set.mem_range_self i)
  have he_mem_K : ∀ l, e l ∈ K := fun l => by
    have : e l ∈ Submodule.span k (Set.range b) := by
      rw [← ht_span]; apply Submodule.subset_span (hrange_e ▸ ⟨l, rfl⟩)
    apply (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; apply hb i)) this
  have hΔx : Coalgebra.comul (R := k) x ∈
    Submodule.span k {s : C ⊗[k] C | ∃ a ∈ K, ∃ b ∈ Submodule.span k (Set.range e), s = a ⊗ₜ[k] b} := by
    rw [← hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rw [hab i]
    apply tmul_mem_span (ha i) (hb_mem i)
  let a' : ↥t → C := fun l => cR (ψ l) (Coalgebra.comul (R := k) x)
  have ha'K : ∀ l, a' l ∈ K := fun l => cR_mem (ψ l) K _ _ hΔx
  have hdag : Coalgebra.comul (R := k) x = ∑ l, a' l ⊗ₜ[k] e l := eq_sum_cR_tmul e ψ hψ K _ hΔx
  have hx_eq : x = ∑ l, Coalgebra.counit (R := k) (e l) • a' l := by
    have h1 : (TensorProduct.rid k C) (LinearMap.lTensor C (Coalgebra.counit (R := k) (A := C))
        (Coalgebra.comul (R := k) x)) = x := by
      rw [Coalgebra.lTensor_counit_comul]; simp
    rw [hdag, map_sum, map_sum] at h1
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul] at h1
    apply h1.symm
  have hΔe : ∀ l, Coalgebra.comul (R := k) (e l) ∈
    Submodule.span k {s : C ⊗[k] C | ∃ a ∈ K, ∃ b ∈ K, s = a ⊗ₜ[k] b} := fun l => hK _ (he_mem_K l)
  let w : ↥t → ↥t → C := fun l m => cR (ψ m) (Coalgebra.comul (R := k) (e l))
  have hwK : ∀ l m, w l m ∈ K := fun l m => cR_mem _ K K _ (hΔe l)
  have hΔa' : ∀ m, Coalgebra.comul (R := k) (a' m) = ∑ l, a' l ⊗ₜ[k] w l m := by
    intro m
    have hco := Coalgebra.coassoc_apply (R := k) x
    have h2 := congrArg (LinearMap.lTensor C (cR (ψ m))) hco
    rw [hdag] at h2
    simp only [map_sum] at h2
    simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, lTensor_cR_assoc, hψ, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h2
    apply h2
  let N : Submodule k C := Submodule.span k (Set.range a')
  have hNK : N ≤ K := Submodule.span_le.mpr (by rintro _ ⟨l, rfl⟩; apply ha'K l)
  have hxN : x ∈ N := by
    rw [hx_eq]
    apply Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self l))
  have hΔN : ∀ y ∈ N, Coalgebra.comul (R := k) y ∈
    Submodule.span k {s : C ⊗[k] C | ∃ a ∈ N, ∃ b ∈ K, s = a ⊗ₜ[k] b} := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    ·
      intro z hz
      obtain ⟨m, rfl⟩ := hz
      rw [hΔa' m]
      apply Submodule.sum_mem _ fun l _ => tmul_mem_span (Submodule.subset_span (Set.mem_range_self l)) (hwK l m)
    · simp
    ·
      intro _ _ _ _ h₁ h₂
      rw [map_add]
      apply Submodule.add_mem _ h₁ h₂
    ·
      intro r _ _ h
      rw [map_smul]
      apply Submodule.smul_mem _ _ h
  obtain ⟨t', ht'_sub, ht'_span, ht'_li⟩ := exists_linearIndependent k (Set.range a')
  let _ : Fintype ↥t' := ((Set.finite_range a').subset ht'_sub).fintype
  let u : ↥t' → C := Subtype.val
  obtain ⟨φ, hφ⟩ := exists_dual_family u ht'_li
  have hspan_u : Submodule.span k (Set.range u) = N := by
    show Submodule.span k (Set.range (Subtype.val : ↥t' → C)) = N
    rw [Subtype.range_coe]; apply ht'_span
  have hu_N : ∀ j, u j ∈ N := fun j => by rw [← hspan_u]; apply Submodule.subset_span ⟨j, rfl⟩
  let v : ↥t' → ↥t' → C := fun j m => cL (φ j) (Coalgebra.comul (R := k) (u m))
  have hvK : ∀ j m, v j m ∈ K := fun j m => cL_mem _ N K _ (hΔN _ (hu_N m))
  have hddag : ∀ m, Coalgebra.comul (R := k) (u m) = ∑ j, u j ⊗ₜ[k] v j m := by
    intro m
    apply eq_sum_tmul_cL u φ hφ K
    rw [hspan_u]
    apply hΔN _ (hu_N m)
  let D : Submodule k C := Submodule.span k (Set.range fun jm : ↥t' × ↥t' => v jm.1 jm.2)
  have hvD : ∀ j m, v j m ∈ D := fun j m => Submodule.subset_span ⟨(j, m), rfl⟩
  have hu_eq : ∀ m, u m = ∑ j, Coalgebra.counit (R := k) (u j) • v j m := by
    intro m
    have h1 : (TensorProduct.lid k C) (LinearMap.rTensor C (Coalgebra.counit (R := k) (A := C))
        (Coalgebra.comul (R := k) (u m))) = u m := by
      rw [Coalgebra.rTensor_counit_comul]; simp
    rw [hddag, map_sum, map_sum] at h1
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at h1
    apply h1.symm
  have huD : ∀ m, u m ∈ D := fun m => by
    rw [hu_eq]
    apply Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvD j m)
  have hND : N ≤ D := by
    rw [← hspan_u]
    apply Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; apply huD j)
  have hΔv : ∀ l m, Coalgebra.comul (R := k) (v l m) = ∑ j, v l j ⊗ₜ[k] v j m := by
    intro l m
    have hco := Coalgebra.coassoc_apply (R := k) (u m)
    have h2 : LinearMap.rTensor C (cL (φ l))
      (LinearMap.rTensor C (Coalgebra.comul (R := k)) (Coalgebra.comul (R := k) (u m))) =
        ∑ j, v l j ⊗ₜ[k] v j m := by
      rw [hddag, map_sum, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, hddag j, map_sum]
      simp only [cL_tmul, hφ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have h3 : LinearMap.rTensor C (cL (φ l)) ((TensorProduct.assoc k C C C).symm
        (LinearMap.lTensor C (Coalgebra.comul (R := k)) (Coalgebra.comul (R := k) (u m)))) =
        Coalgebra.comul (R := k) (v l m) := by
      rw [hddag, map_sum, map_sum, map_sum]
      simp only [LinearMap.lTensor_tmul, rTensor_cL_assoc_symm, hφ, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [← hco, LinearEquiv.symm_apply_apply] at h3
    rw [← h3, h2]
  refine ⟨D, ?_, ?_, hND hxN, ?_⟩
  · apply Submodule.span_le.mpr (by rintro _ ⟨⟨j, m⟩, rfl⟩; apply hvK j m)
  · apply FiniteDimensional.span_of_finite k (Set.finite_range _)
  ·
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    ·
      intro z hz
      obtain ⟨⟨l, m⟩, rfl⟩ := hz
      show Coalgebra.comul (R := k) (v l m) ∈ _
      rw [hΔv l m]
      apply Submodule.sum_mem _ fun j _ => tmul_mem_span (hvD l j) (hvD j m)
    · simp
    ·
      intro _ _ _ _ h₁ h₂
      rw [map_add]
      apply Submodule.add_mem _ h₁ h₂
    ·
      intro r _ _ h
      rw [map_smul]
      apply Submodule.smul_mem _ _ h


-- created on 2026-10-20
