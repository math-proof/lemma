import Mathlib
import sympy.Basic
set_option backward.isDefEq.respectTransparency false
open Polynomial


private lemma monogenic_main
  {R' : Type u} [CommRing R'] [IsLocalRing R']
  {R : Type v} [CommRing R] [IsLocalRing R]
  {C : Type w} [CommRing C] [Algebra R C]
  {ι : Type x} [Fintype ι]
  {π : R' →+* R} {e : Module.Basis ι R C} {i₀ : ι} {y : C}
-- given
  (hπ : Function.Surjective π)
  (he : e i₀ = 1)
  (hy : ∀ z : C, ∃ q : R[X], z - aeval y q ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R C)) :
-- imply
  ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra R' C') (e' : Module.Basis ι R' C') (σ : C' →+* C),
    e' i₀ = 1 ∧ (∀ r, σ (algebraMap R' C' r) = algebraMap R C (π r)) ∧ ∀ i, σ (e' i) = e i := by
-- proof
  classical
  let _ : Module.Free R C := Module.Free.of_basis e
  let _ : Module.Finite R C := Module.Finite.of_basis e
  let _ : Nonempty ι := ⟨i₀⟩
  have hspan_all : (⊤ : Submodule R C) ≤ Submodule.span R (Set.range fun k : ℕ => y ^ k) := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    intro z _
    obtain ⟨q, hq⟩ := hy z
    have h1 : aeval y q ∈ Submodule.span R (Set.range fun k : ℕ => y ^ k) := by
      rw [aeval_eq_sum_range]
      refine Submodule.sum_mem _ fun k _ => ?_
      apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨k, rfl⟩
    have h2 : z = aeval y q + (z - aeval y q) := by ring
    rw [h2]
    apply Submodule.add_mem_sup h1 hq
  set χ : R[X] := (Algebra.lmul R C y).charpoly with hχdef
  have hχm : χ.Monic := LinearMap.charpoly_monic _
  have hχdeg : χ.natDegree = Fintype.card ι := by
    rw [hχdef, LinearMap.charpoly_natDegree, Module.finrank_eq_card_basis e]
  have hχy : aeval y χ = 0 := by
    apply Algebra.lmul_injective (R := R) <| by
      rw [← Polynomial.aeval_algHom_apply, map_zero]
      apply LinearMap.aeval_self_charpoly _
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hχ1 : χ ≠ 1 := by
    intro h
    have := congrArg natDegree h
    rw [hχdeg, natDegree_one] at this
    omega
  obtain ⟨χ', hχ'map, hχ'deg, hχ'm⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic (Polynomial.mem_lifts_of_surjective hπ χ) hχm
  set d : ℕ := χ'.natDegree with hddef
  have hd : d = Fintype.card ι := by
    rw [hχ'deg, hχdeg]
  have hd0 : 0 < d := by
    rw [hd]
    apply hcard
  set v : Fin d → C := fun j => y ^ (j : ℕ) with hvdef
  have hv_span : (⊤ : Submodule R C) ≤ Submodule.span R (Set.range v) := by
    refine hspan_all.trans (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    have hk : y ^ k = aeval y ((X ^ k).modByMonic χ) := by
      rw [aeval_modByMonic_eq_self_of_root hχy, map_pow, aeval_X]
    have hlt : ((X ^ k).modByMonic χ).natDegree < d := by
      rw [hd, ← hχdeg]
      apply natDegree_modByMonic_lt _ hχm hχ1
    change y ^ k ∈ Submodule.span R (Set.range v)
    rw [hk, aeval_eq_sum_range' hlt, ← Fin.sum_univ_eq_sum_range]
    refine Submodule.sum_mem _ fun j _ => ?_
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨j, rfl⟩
  let ιd : ι ≃ Fin d := Fintype.equivFinOfCardEq hd.symm
  have hv_li : LinearIndependent R v := by
    let L : Finsupp (Fin d) R →ₗ[R] C := Finsupp.linearCombination R v
    have hL : Function.Surjective L := by
      rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
      apply top_le_iff.mp hv_span
    let inj : Finsupp (Fin d) R →ₗ[R] C :=
      LinearMap.comp e.repr.symm.toLinearMap (Finsupp.domLCongr ιd.symm).toLinearMap
    apply OrzechProperty.injective_of_surjective_of_injective inj L
      (e.repr.symm.injective.comp (Finsupp.domLCongr ιd.symm).injective) hL
  let vB : Module.Basis (Fin d) R C := Module.Basis.mk hv_li hv_span
  have hvB : ∀ j, vB j = y ^ (j : ℕ) := fun j => by
    rw [Module.Basis.mk_apply]
  let _ : Module.Free R' (AdjoinRoot χ') := hχ'm.free_adjoinRoot
  let _ : Module.Finite R' (AdjoinRoot χ') := hχ'm.finite_adjoinRoot
  let pb : PowerBasis R' (AdjoinRoot χ') := AdjoinRoot.powerBasis' hχ'm
  have hpbdim : pb.dim = d := rfl
  have hpb : ∀ j : Fin d, pb.basis j = AdjoinRoot.root χ' ^ (j : ℕ) := fun j => by
    rw [PowerBasis.coe_basis]
    rfl
  have hev : χ'.eval₂ ((algebraMap R C).comp π) y = 0 := by
    rw [← Polynomial.eval₂_map, hχ'map]
    apply hχy
  let σ : AdjoinRoot χ' →+* C := AdjoinRoot.lift ((algebraMap R C).comp π) y hev
  have hσ_of : ∀ r, σ (algebraMap R' (AdjoinRoot χ') r) = algebraMap R C (π r) := fun r => by
    rw [AdjoinRoot.algebraMap_eq]
    apply AdjoinRoot.lift_of hev
  have hσ_root : ∀ k : ℕ, σ (AdjoinRoot.root χ' ^ k) = y ^ k := fun k => by
    rw [map_pow, AdjoinRoot.lift_root]
  have hσ_smul : ∀ (r : R') (c : AdjoinRoot χ'), σ (r • c) = π r • σ c := fun r c => by
    rw [Algebra.smul_def, map_mul, hσ_of, ← Algebra.smul_def]
  have hσ_sum : ∀ a : Fin d → R', σ (∑ j, a j • pb.basis j) = ∑ j, π (a j) • v j := fun a => by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hσ_smul, hpb, hσ_root]
  have hkerσ : ∀ c : AdjoinRoot χ', σ c = 0 → c ∈ (RingHom.ker π) • (⊤ : Submodule R' (AdjoinRoot χ')) := by
    intro c hc
    have hc' : c = ∑ j : Fin d, pb.basis.repr c j • pb.basis j := (pb.basis.sum_repr c).symm
    rw [hc', hσ_sum] at hc
    have hzero : ∀ j, π (pb.basis.repr c j) = 0 := fun j =>
      linearIndependent_iff'.mp hv_li Finset.univ (fun j => π (pb.basis.repr c j)) hc j
        (Finset.mem_univ j)
    rw [hc']
    apply Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem_smul (RingHom.mem_ker.2 (hzero j)) Submodule.mem_top
  let s : R → R' := Function.surjInv hπ
  have hs : ∀ r, π (s r) = r := Function.surjInv_eq hπ
  let j₀ : Fin d := ⟨0, hd0⟩
  have hvB0 : vB j₀ = 1 := by
    rw [hvB]
    simp [j₀]
  have hP0 : ∀ j : Fin d, vB.repr (e i₀) j = if j = j₀ then 1 else 0 := fun j => by
    rw [he, ← hvB0, vB.repr_self, Finsupp.single_apply]
    if h : j = j₀ then
      rw [ite_eq_left h, ite_eq_left h.symm]
    else
      rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  let P' : ι → Fin d → R' := fun i j =>
    if i = i₀ then (if j = j₀ then 1 else 0) else s (vB.repr (e i) j)
  have hP' : ∀ i j, π (P' i j) = vB.repr (e i) j := by
    intro i j
    if hi : i = i₀ then
      subst hi
      simp only [P', ite_true, hP0]
      split_ifs
      · simp
      · simp
    else
      simp only [P', ite_eq_right hi, hs]
  let ev : ι → AdjoinRoot χ' := fun i => ∑ j, P' i j • pb.basis j
  have hσev : ∀ i, σ (ev i) = e i := fun i => by
    change σ (∑ j, P' i j • pb.basis j) = e i
    rw [hσ_sum]
    conv_rhs => rw [← vB.sum_repr (e i)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hP', hvB]
  have hev0 : ev i₀ = 1 := by
    change ∑ j, P' i₀ j • pb.basis j = 1
    rw [Finset.sum_eq_single j₀]
    ·
      simp only [P', ite_true, one_smul, hpb]
      simp [j₀]
    ·
      intro j _ hj
      simp only [P', ite_true, ite_eq_right hj, zero_smul]
    ·
      intro h
      apply absurd (Finset.mem_univ j₀) h
  have hkerπ : RingHom.ker π ≤ (⊥ : Ideal R').jacobson :=
    (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π)).trans
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have hev_span : (⊤ : Submodule R' (AdjoinRoot χ')) ≤ Submodule.span R' (Set.range ev) := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hkerπ
    intro c _
    let c'' : AdjoinRoot χ' := ∑ i, s (e.repr (σ c) i) • ev i
    have hc'' : c'' ∈ Submodule.span R' (Set.range ev) :=
      Submodule.sum_mem _ fun i _ => by
        apply Submodule.smul_mem
        apply Submodule.subset_span
        refine ⟨i, rfl⟩
    have hσc'' : σ c'' = σ c := by
      change σ (∑ i, s (e.repr (σ c) i) • ev i) = σ c
      rw [map_sum]
      conv_rhs => rw [← e.sum_repr (σ c)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hσ_smul, hs, hσev]
    have hdiff : c - c'' ∈ (RingHom.ker π) • (⊤ : Submodule R' (AdjoinRoot χ')) :=
      hkerσ _ (by rw [map_sub, hσc'', sub_self])
    have : c = c'' + (c - c'') := by ring
    rw [this]
    apply Submodule.add_mem_sup hc'' hdiff
  have hev_li : LinearIndependent R' ev := by
    let L : Finsupp ι R' →ₗ[R'] AdjoinRoot χ' := Finsupp.linearCombination R' ev
    have hL : Function.Surjective L := by
      rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
      apply top_le_iff.mp hev_span
    let inj : Finsupp ι R' →ₗ[R'] AdjoinRoot χ' :=
      LinearMap.comp pb.basis.repr.symm.toLinearMap (Finsupp.domLCongr ιd).toLinearMap
    apply OrzechProperty.injective_of_surjective_of_injective inj L
      (pb.basis.repr.symm.injective.comp (Finsupp.domLCongr ιd).injective) hL
  let e' : Module.Basis ι R' (AdjoinRoot χ') := Module.Basis.mk hev_li hev_span
  refine ⟨AdjoinRoot χ', inferInstance, inferInstance, e', σ, ?_, hσ_of, fun i => ?_⟩
  ·
    rw [Module.Basis.mk_apply]
    apply hev0
  ·
    rw [Module.Basis.mk_apply]
    apply hσev i


/--
[Algebra_exists_lift_basis_of_surjective_of_monogenic_specialFibre](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_lift_basis_of_surjective_of_monogenic_specialFibre.lean)
-/
@[path]
private lemma main
  {R' : Type u} [CommRing R'] [IsLocalRing R']
  {R : Type v} [CommRing R] [IsLocalRing R]
  {C : Type w} [CommRing C] [Algebra R C]
  {ι : Type x} [Fintype ι]
  {π : R' →+* R} {e : Module.Basis ι R C} {i₀ : ι}
-- given
  (hπ : Function.Surjective π)
  (he : e i₀ = 1)
  (hmono : ∃ y : C, ∀ z : C, ∃ q : R[X], z - aeval y q ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R C)) :
-- imply
  ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra R' C') (e' : Module.Basis ι R' C') (σ : C' →+* C),
    e' i₀ = 1 ∧ (∀ r, σ (algebraMap R' C' r) = algebraMap R C (π r)) ∧ ∀ i, σ (e' i) = e i := by
-- proof
  obtain ⟨y, hy⟩ := hmono
  apply monogenic_main (π := π) (e := e) (i₀ := i₀) (y := y) hπ he hy


-- created on 2026-10-13
