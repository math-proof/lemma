import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfProbability.code.PoissonConvergence
open MeasureTheory ProbabilityTheory Filter Real Finset
open scoped ENNReal NNReal Topology Nat


namespace ProbabilityTheory

/--
[bernoulli_sum_pmf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PoissonConvergence.lean)
-/
@[path]
lemma bernoulli_sum_pmf
  (p_i)
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {m : ℕ}
  {X : Fin m → Ω → ℕ}
  {p : Fin m → ℝ}
  {j : ℕ}
-- given
  (hBernoulli : ∀ i, IsBernoulliRV (X i) μ (p i))
  (hIndep : iIndepFun X μ)
  (hMeas : ∀ i, Measurable (X i)) :
-- imply
  (μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j})).toReal = ∑ A ∈ Finset.univ.powersetCard j, (∏ i ∈ A, p i) * (∏ i ∈ Finset.univ \ A, (1 - p i)) := by
-- proof
  classical
  set PC := (Finset.univ : Finset (Fin m)).powersetCard j with hPC_def
  have hFsubS : (⋃ A ∈ PC,
    ⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ)) ⊆
    (fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j} := by
    apply Set.iUnion₂_subset; intro A hA ω hω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢
    rw [Finset.mem_powersetCard] at hA
    calc ∑ i : Fin m, X i ω
      = ∑ i, if i ∈ A then 1 else 0 := Finset.sum_congr rfl (fun i _ => hω i)
      _ = A.card := by simp
      _ = j := hA.2
  have hdiff_null : μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j} \
    ⋃ A ∈ PC, ⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ)) = 0 := by
    have hae : ∀ᵐ ω ∂μ, ∀ i, X i ω = 0 ∨ X i ω = 1 := by
      rw [Filter.eventually_all]; intro i
      suffices μ {ω | ¬(X i ω = 0 ∨ X i ω = 1)} = 0 from this
      have heq : {ω | ¬(X i ω = 0 ∨ X i ω = 1)} = (X i ⁻¹' {0} ∪ X i ⁻¹' {1})ᶜ := by
        ext; simp
      rw [heq]
      have hd : Disjoint (X i ⁻¹' {0}) (X i ⁻¹' {1}) :=
        Set.disjoint_left.mpr (fun ω h0 h1 => by
          simp [Set.mem_preimage] at h0 h1; omega)
      have hfin : μ (X i ⁻¹' {0} ∪ X i ⁻¹' {1}) ≠ ⊤ := by
        rw [measure_union hd ((hMeas i) (measurableSet_singleton 1)),
          (hBernoulli i).2.2.1, (hBernoulli i).2.2.2,
          ← ENNReal.ofReal_add (by linarith [(hBernoulli i).1, (hBernoulli i).2.1])
            (hBernoulli i).1]
        simp
      rw [measure_compl (.union ((hMeas i) (measurableSet_singleton 0))
        ((hMeas i) (measurableSet_singleton 1))) hfin]
      rw [measure_union hd ((hMeas i) (measurableSet_singleton 1)),
        (hBernoulli i).2.2.1, (hBernoulli i).2.2.2,
        ← ENNReal.ofReal_add (by linarith [(hBernoulli i).1, (hBernoulli i).2.1])
          (hBernoulli i).1]
      simp
    apply le_antisymm _ (zero_le _)
    calc μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j} \
      ⋃ A ∈ PC, ⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ))
      ≤ μ {ω | ¬∀ i, X i ω = 0 ∨ X i ω = 1} := by
        apply measure_mono; intro ω ⟨hω_S, hω_not⟩
        simp only [Set.mem_setOf_eq]; intro h_all; apply hω_not
        simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
        refine ⟨Finset.univ.filter (fun i => X i ω = 1), ?_, ?_⟩
        · rw [Finset.mem_powersetCard]; exact ⟨Finset.filter_subset _ _, by
          rw [Finset.card_filter]
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω_S
          have key : ∀ i : Fin m, X i ω = if X i ω = 1 then 1 else 0 := by
            intro i; rcases h_all i with h | h <;> simp [h]
          rw [Finset.sum_congr rfl (fun i _ => key i)] at hω_S; simpa using hω_S⟩
        · intro i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          obtain h | h <;> simp [h] := h_all i
      _ ≤ 0 := by rw [ae_iff] at hae; exact hae.le
  have hS_eq : μ ((fun ω => ∑ i : Fin m, X i ω) ⁻¹' {↑j}) =
    μ (⋃ A ∈ PC, ⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ)) :=
    (measure_eq_measure_of_null_diff hFsubS hdiff_null).symm
  have hF_disj : (PC : Set (Finset (Fin m))).PairwiseDisjoint
    (fun A => ⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ)) := by
    intro A _ B _ hAB
    simp only [Function.onFun, Set.disjoint_left, Set.mem_iInter, Set.mem_preimage,
      Set.mem_singleton_iff]
    intro ω hA hB; apply hAB; ext i
    constructor
    · intro hi
      have hAi := hA i; simp only [hi, ↓reduceIte] at hAi
      have hBi := hB i; rw [hAi] at hBi; simpa using hBi
    · intro hi
      have hBi := hB i; simp only [hi, ↓reduceIte] at hBi
      have hAi := hA i; rw [hBi] at hAi; simpa using hAi
  have hF_meas : ∀ A ∈ PC, MeasurableSet
    (⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ)) := by
    intro A _; exact MeasurableSet.iInter (fun i => (hMeas i) (measurableSet_singleton _))
  have hbiUnion : μ (⋃ A ∈ PC,
    ⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ)) =
    ∑ A ∈ PC, μ (⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ)) :=
    measure_biUnion_finset hF_disj hF_meas
  have hF_indep : ∀ A : Finset (Fin m),
    μ (⋂ i : Fin m, X i ⁻¹' ({if i ∈ A then 1 else 0} : Set ℕ)) =
      ∏ i : Fin m, ENNReal.ofReal (if i ∈ A then p i else 1 - p i) := by
    intro A
    rw [hIndep.meas_iInter (fun i =>
      ⟨{if i ∈ A then 1 else 0}, measurableSet_singleton _, rfl⟩)]
    congr 1; ext i; split_ifs with h
    · exact (hBernoulli i).2.2.2
    · exact (hBernoulli i).2.2.1
  rw [hS_eq, hbiUnion]
  rw [ENNReal.toReal_sum (fun A _ => ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
    (measure_mono (Set.subset_univ _)))]
  congr 1; ext A
  rw [hF_indep A, ENNReal.toReal_prod]
  have h_toReal : ∀ i : Fin m,
    (ENNReal.ofReal (if i ∈ A then p i else 1 - p i)).toReal =
      if i ∈ A then p i else 1 - p i := by
    intro i; split_ifs with h
    · exact ENNReal.toReal_ofReal (hBernoulli i).1
    · exact ENNReal.toReal_ofReal (by linarith [(hBernoulli i).2.1])
  rw [Finset.prod_congr rfl (fun i _ => h_toReal i)]
  rw [show (∏ i ∈ A, p i) = ∏ i ∈ A, (if i ∈ A then p i else 1 - p i) from
    Finset.prod_congr rfl (fun i hi => by simp [hi])]
  rw [show (∏ i ∈ Finset.univ \ A, (1 - p i)) =
    ∏ i ∈ Finset.univ \ A, (if i ∈ A then p i else 1 - p i) from
    Finset.prod_congr rfl (fun i hi => by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi; simp [hi])]
  rw [← Finset.prod_union disjoint_sdiff_self_right,
    Finset.union_sdiff_of_subset (Finset.subset_univ A)]
/-- Analytic core of Poisson convergence: if `max_i p_{n,i} → 0` and `∑_i p_{n,i} → λ` as
`n → ∞`, then the `j`-th elementary symmetric polynomial expression
`∑_{|A|=j} ∏_{i ∈ A} p_{n,i} · ∏_{i ∉ A} (1 - p_{n,i})` converges to the Poisson pmf
`λ^j e^{-λ} / j!`. -/

end ProbabilityTheory


-- created on 2026-10-23
