import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.SL2Classification
open Complex SL2SimpleModule
open SL2SimpleModule


/--
[SL2IrredGKModule.Realization.exists'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Classification.lean)
-/
@[path]
private lemma SL2IrredGKModule.Realization.exists'
  {μ : SL2IrredGKModule}
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  {K : Type*}
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)} :
-- imply
  Nonempty (SL2IrredGKModule.Realization μ 𝔤 K 𝔨 Ad) :=
-- proof
  sl2IrredGKModule_realization_exists μ 𝔤 K 𝔨 Ad
open Complex

/--
[GKModule.isIrreducibleGKModule_of_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Classification.lean)
-/
@[path]
private lemma GKModule.isIrreducibleGKModule_of_iso
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  [AddCommGroup W]
  [Module ℂ W]
  [LieRingModule 𝔤 W]
  [LieModule ℂ 𝔤 W]
  {M : GKModule 𝔤 K 𝔨 Ad V}
  {N : GKModule 𝔤 K 𝔨 Ad W}
-- given
  (hiso : M.IsIsomorphicGK N)
  (hirr : M.IsIrreducibleGKModule) :
-- imply
  N.IsIrreducibleGKModule := by
-- proof
  obtain ⟨φ, hφ⟩ := hiso
  let e := LinearEquiv.ofBijective φ.toLinearMap hφ
  intro U hU
  let U' := U.comap e.toLinearMap
  have hU' : M.IsSubmodule U' := by
    constructor
    ·
      intro X v (hv : e.toLinearMap v ∈ U)
      show e.toLinearMap ⁅X, v⁆ ∈ U
      rw [show e.toLinearMap ⁅X, v⁆ = φ.toLinearMap ⁅X, v⁆ from rfl, φ.lie_comm]
      exact hU.lie_invariant X (e.toLinearMap v) hv
    ·
      intro k v (hv : e.toLinearMap v ∈ U)
      show e.toLinearMap (M.σ k v) ∈ U
      rw [show e.toLinearMap (M.σ k v) = φ.toLinearMap (M.σ k v) from rfl, φ.group_comm]
      exact hU.group_invariant k (e.toLinearMap v) hv
  obtain h | h := hirr U' hU'
  ·
    left
    rw [Submodule.eq_bot_iff] at h ⊢
    intro w hw
    have hew : e.symm w ∈ U' := by
      change e.toLinearMap (e.symm w) ∈ U
      simp [hw]
    have h0 := h (e.symm w) hew
    have : w = 0 := by
      have : e (e.symm w) = e 0 := by rw [h0]
      simp at this
      exact this
    exact this
  ·
    right
    rw [Submodule.eq_top_iff'] at h ⊢
    intro w
    have : e.symm w ∈ U' := h (e.symm w)
    show w ∈ U
    have : e.toLinearMap (e.symm w) ∈ U := this
    rwa [show e.toLinearMap (e.symm w) = w from e.apply_symm_apply w] at this

/--
[sl2_classification_existence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Classification.lean)
-/
@[path]
private lemma sl2_classification_existence
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  {K : Type*}
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  {V : Type*}
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {M : GKModule 𝔤 K 𝔨 Ad V}
  {M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V}
-- given
  (hirr : M.IsIrreducibleGKModule)
  (hadm : M.IsAdmissible) :
-- imply
  ∃ (μ : SL2SimpleModule), ∃ (R : SL2IrredGKModule.Realization.{_, _, 0} (match μ with | .finiteDim m => .finiteDim m | .discreteSeriesMinus m _hm => if h2 : m ≥ 2 then .discreteSeriesMinus m h2 else .limitDiscreteMinus | .discreteSeriesPlus m _hm => if h2 : m ≥ 2 then .discreteSeriesPlus m h2 else .limitDiscretePlus | .principalSeriesEven s _ => .principalSeries s 0 | .principalSeriesOdd s _ => .principalSeries s 1) 𝔤 K 𝔨 Ad), M.IsIsomorphicGK R.gkmod := by
-- proof
  obtain ⟨μ₀, R₀, hiso₀⟩ := sl2_gk_classification 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm
  match μ₀ with
  | .finiteDim n =>
    exact ⟨.finiteDim n, R₀, hiso₀⟩
  | .principalSeries ν ε =>
    by_cases hε : ε = 0
    ·
      by_cases hν : IsOddInteger ν
      ·
        subst hε
        exact absurd (GKModule.isIrreducibleGKModule_of_iso hiso₀ hirr)
          (principalSeries_even_reducible ν hν R₀)
      ·
        subst hε
        exact ⟨.principalSeriesEven ν hν, R₀, hiso₀⟩
    ·
      have hε1 : ε = 1 := by
        have : ε = 0 ∨ ε = 1 := by
          fin_cases ε
          · left; rfl
          · right; rfl
        exact this.resolve_left hε
      by_cases hν : IsEvenInteger ν
      ·
        subst hε1
        exact absurd (GKModule.isIrreducibleGKModule_of_iso hiso₀ hirr)
          (principalSeries_odd_reducible ν hν R₀)
      ·
        subst hε1
        exact ⟨.principalSeriesOdd ν hν, R₀, hiso₀⟩
  | .discreteSeriesPlus n hn =>
    refine ⟨.discreteSeriesPlus n (by omega), ⟨R₀.W, R₀.gkmod, R₀.casimirScalar, ?_⟩, hiso₀⟩
    rw [R₀.casimir_eq]; simp [hn]
  | .discreteSeriesMinus n hn =>
    refine ⟨.discreteSeriesMinus n (by omega), ⟨R₀.W, R₀.gkmod, R₀.casimirScalar, ?_⟩, hiso₀⟩
    rw [R₀.casimir_eq]; simp [hn]
  | .limitDiscretePlus =>
    refine ⟨.discreteSeriesPlus 1 (by omega), ⟨R₀.W, R₀.gkmod, R₀.casimirScalar, ?_⟩, hiso₀⟩
    rw [R₀.casimir_eq]; simp [show ¬ (1 : ℕ) ≥ 2 from by omega]
  | .limitDiscreteMinus =>
    refine ⟨.discreteSeriesMinus 1 (by omega), ⟨R₀.W, R₀.gkmod, R₀.casimirScalar, ?_⟩, hiso₀⟩
    rw [R₀.casimir_eq]; simp [show ¬ (1 : ℕ) ≥ 2 from by omega]

/--
[sl2_principalSeriesEven_neg_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Classification.lean)
-/
@[path]
private lemma sl2_principalSeriesEven_neg_iso
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  {K : Type*}
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  {s : ℂ}
  {R₁ : SL2IrredGKModule.Realization (.principalSeries s 0) 𝔤 K 𝔨 Ad}
  {R₂ : SL2IrredGKModule.Realization (.principalSeries (-s) 0) 𝔤 K 𝔨 Ad}
-- given
  (hs : ¬ IsOddInteger s)
  (hs' : ¬ IsOddInteger (-s)) :
-- imply
  R₁.gkmod.IsIsomorphicGK R₂.gkmod :=
-- proof
  principalSeries_neg_iso s 0 R₁ R₂

/--
[sl2_principalSeriesOdd_neg_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Classification.lean)
-/
@[path]
private lemma sl2_principalSeriesOdd_neg_iso
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  {K : Type*}
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  {s : ℂ}
  {R₁ : SL2IrredGKModule.Realization (.principalSeries s 1) 𝔤 K 𝔨 Ad}
  {R₂ : SL2IrredGKModule.Realization (.principalSeries (-s) 1) 𝔤 K 𝔨 Ad}
-- given
  (hs : ¬ IsEvenInteger s)
  (hs' : ¬ IsEvenInteger (-s)) :
-- imply
  R₁.gkmod.IsIsomorphicGK R₂.gkmod :=
-- proof
  principalSeries_neg_iso s 1 R₁ R₂

/--
[sl2_classification_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Classification.lean)
-/
@[path]
private lemma sl2_classification_uniqueness
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  {K : Type*}
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  {μ ν : SL2SimpleModule}
-- given
  (Rμ : SL2IrredGKModule.Realization (match μ with | .finiteDim m => .finiteDim m | .discreteSeriesMinus m hm => if h2 : m ≥ 2 then .discreteSeriesMinus m h2 else .limitDiscreteMinus | .discreteSeriesPlus m hm => if h2 : m ≥ 2 then .discreteSeriesPlus m h2 else .limitDiscretePlus | .principalSeriesEven s _ => .principalSeries s 0 | .principalSeriesOdd s _ => .principalSeries s 1) 𝔤 K 𝔨 Ad)
  (Rν : SL2IrredGKModule.Realization (match ν with | .finiteDim m => .finiteDim m | .discreteSeriesMinus m hm => if h2 : m ≥ 2 then .discreteSeriesMinus m h2 else .limitDiscreteMinus | .discreteSeriesPlus m hm => if h2 : m ≥ 2 then .discreteSeriesPlus m h2 else .limitDiscretePlus | .principalSeriesEven s _ => .principalSeries s 0 | .principalSeriesOdd s _ => .principalSeries s 1) 𝔤 K 𝔨 Ad)
  (hiso : Rμ.gkmod.IsIsomorphicGK Rν.gkmod) :
-- imply
  μ.IsIsomorphic ν := by
-- proof
  have hmatch := sl2_iso_implies_label_match μ.toIrredGK ν.toIrredGK Rμ Rν hiso
  obtain heq | ⟨s', ε', hμ_ps, hν_ps⟩ := hmatch
  ·
    cases μ with
    | finiteDim m =>
      cases ν with
      | finiteDim m' => simp [toIrredGK] at heq; exact heq
      | discreteSeriesMinus m' hm' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | discreteSeriesPlus m' hm' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | principalSeriesEven s' hs' => simp [toIrredGK] at heq
      | principalSeriesOdd s' hs' => simp [toIrredGK] at heq
    | discreteSeriesMinus m hm =>
      cases ν with
      | finiteDim m' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | discreteSeriesMinus m' hm' =>
        simp only [toIrredGK] at heq; split_ifs at heq with h1 h2 <;>
          (simp only [IsIsomorphic]; try simp_all [SL2IrredGKModule.noConfusion]) <;> omega
      | discreteSeriesPlus m' hm' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | principalSeriesEven s' hs' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | principalSeriesOdd s' hs' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
    | discreteSeriesPlus m hm =>
      cases ν with
      | finiteDim m' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | discreteSeriesMinus m' hm' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | discreteSeriesPlus m' hm' =>
        simp only [toIrredGK] at heq; split_ifs at heq with h1 h2 <;>
          (simp only [IsIsomorphic]; try simp_all [SL2IrredGKModule.noConfusion]) <;> omega
      | principalSeriesEven s' hs' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | principalSeriesOdd s' hs' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
    | principalSeriesEven sμ hsμ =>
      cases ν with
      | finiteDim m' => simp [toIrredGK] at heq
      | discreteSeriesMinus m' hm' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | discreteSeriesPlus m' hm' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | principalSeriesEven s' hs' =>
        simp only [toIrredGK] at heq
        simp only [IsIsomorphic]
        left; exact (SL2IrredGKModule.principalSeries.inj heq).1
      | principalSeriesOdd s' hs' => simp [toIrredGK] at heq
    | principalSeriesOdd sμ hsμ =>
      cases ν with
      | finiteDim m' => simp [toIrredGK] at heq
      | discreteSeriesMinus m' hm' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | discreteSeriesPlus m' hm' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | principalSeriesEven s' hs' => simp [toIrredGK] at heq
      | principalSeriesOdd s' hs' =>
        simp only [toIrredGK] at heq
        simp only [IsIsomorphic]
        left; exact (SL2IrredGKModule.principalSeries.inj heq).1
  ·
    cases μ with
    | finiteDim m => simp [toIrredGK] at hμ_ps
    | discreteSeriesMinus m hm =>
      simp [toIrredGK] at hμ_ps; split_ifs at hμ_ps <;> simp_all [SL2IrredGKModule.noConfusion]
    | discreteSeriesPlus m hm =>
      simp [toIrredGK] at hμ_ps; split_ifs at hμ_ps <;> simp_all [SL2IrredGKModule.noConfusion]
    | principalSeriesEven sμ hsμ =>
      cases ν with
      | finiteDim m' => simp [toIrredGK] at hν_ps
      | discreteSeriesMinus m' hm' =>
        simp [toIrredGK] at hν_ps; split_ifs at hν_ps <;> simp_all [SL2IrredGKModule.noConfusion]
      | discreteSeriesPlus m' hm' =>
        simp [toIrredGK] at hν_ps; split_ifs at hν_ps <;> simp_all [SL2IrredGKModule.noConfusion]
      | principalSeriesEven sν hsν =>
        simp only [toIrredGK] at hμ_ps hν_ps
        simp only [IsIsomorphic]
        obtain ⟨rfl, rfl⟩ := SL2IrredGKModule.principalSeries.inj hμ_ps
        obtain ⟨h_neg, _⟩ := SL2IrredGKModule.principalSeries.inj hν_ps
        right; rw [h_neg]; ring
      | principalSeriesOdd sν hsν =>
        simp only [toIrredGK] at hμ_ps hν_ps
        have h1 := SL2IrredGKModule.principalSeries.inj hμ_ps
        have h2 := SL2IrredGKModule.principalSeries.inj hν_ps
        exact absurd (h1.2.trans h2.2.symm) (by decide)
    | principalSeriesOdd sμ hsμ =>
      cases ν with
      | finiteDim m' => simp [toIrredGK] at hν_ps
      | discreteSeriesMinus m' hm' =>
        simp [toIrredGK] at hν_ps; split_ifs at hν_ps <;> simp_all [SL2IrredGKModule.noConfusion]
      | discreteSeriesPlus m' hm' =>
        simp [toIrredGK] at hν_ps; split_ifs at hν_ps <;> simp_all [SL2IrredGKModule.noConfusion]
      | principalSeriesEven sν hsν =>
        simp only [toIrredGK] at hμ_ps hν_ps
        have h1 := SL2IrredGKModule.principalSeries.inj hμ_ps
        have h2 := SL2IrredGKModule.principalSeries.inj hν_ps
        exact absurd (h1.2.trans h2.2.symm) (by decide)
      | principalSeriesOdd sν hsν =>
        simp only [toIrredGK] at hμ_ps hν_ps
        simp only [IsIsomorphic]
        obtain ⟨rfl, rfl⟩ := SL2IrredGKModule.principalSeries.inj hμ_ps
        obtain ⟨h_neg, _⟩ := SL2IrredGKModule.principalSeries.inj hν_ps
        right; rw [h_neg]; ring


-- created on 2026-10-23
-- updated on 2026-10-24
