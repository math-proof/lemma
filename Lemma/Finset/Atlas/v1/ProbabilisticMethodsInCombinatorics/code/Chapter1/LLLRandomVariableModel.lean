import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory ENNReal Set Finset Real


namespace LovaszLocalLemma

/--
[cond_le_of_indepSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/LLLRandomVariableModel.lean)
-/
@[path]
lemma cond_le_of_indepSet
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {s t : Set Ω}
-- given
  (hs : MeasurableSet s)
  (h : IndepSet t s μ) :
-- imply
  μ[t | s] ≤ μ t := by
-- proof
  rw [cond_apply hs]
  rw [show μ (s ∩ t) = μ s * μ t from by rw [Set.inter_comm, h.measure_inter_eq_mul, mul_comm]]
  calc (μ s)⁻¹ * (μ s * μ t) = ((μ s)⁻¹ * μ s) * μ t := by ring
    _ ≤ 1 * μ t := by gcongr; exact ENNReal.inv_mul_le_one (μ s)
    _ = μ t := one_mul _

end LovaszLocalLemma

namespace LovaszLocalLemma

/--
[indepSet_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/LLLRandomVariableModel.lean)
-/
@[path]
lemma indepSet_of_disjoint_support
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {N m_count : ℕ}
  {β : Fin N → Type*}
  [∀ j, MeasurableSpace (β j)]
  {X : (j : Fin N) → Ω → β j}
  {E : Fin m_count → Set Ω}
  {B : Fin m_count → Finset (Fin N)}
  {i : Fin m_count}
  {S : Finset (Fin m_count)}
-- given
  (hX_indep : iIndepFun X μ)
  (hX_meas : ∀ j, Measurable (X j))
  (hE_dep : ∀ i, @MeasurableSet Ω (⨆ j ∈ B i, MeasurableSpace.comap (X j) inferInstance) (E i))
  (h_disj : ∀ j ∈ S, Disjoint (B i : Set (Fin N)) (B j : Set (Fin N))) :
-- imply
  IndepSet (E i) (⋂ j ∈ (S : Set (Fin m_count)), (E j)ᶜ) μ := by
-- proof
  classical
  set m_sa := fun j : Fin N => MeasurableSpace.comap (X j) inferInstance
  have h_le : ∀ j, m_sa j ≤ ‹MeasurableSpace Ω› :=
    fun j => MeasurableSpace.comap_le_iff_le_map.mpr (hX_meas j)
  have h_iIndep : iIndep m_sa μ := (iIndepFun_iff_iIndep _ X μ).mp hX_indep
  set S_vars := S.biUnion B
  have h_disj_sets : Disjoint (↑(B i) : Set (Fin N)) (↑S_vars : Set (Fin N)) := by
    rw [Finset.coe_biUnion]
    simp only [Set.disjoint_iUnion_right]
    exact fun j hj => h_disj j hj
  have h_indep_sigma := indep_iSup_of_disjoint h_le h_iIndep h_disj_sets
  have hEi_meas : @MeasurableSet Ω (⨆ k ∈ (B i : Set (Fin N)), m_sa k) (E i) := hE_dep i
  have h_avoid_meas : @MeasurableSet Ω (⨆ k ∈ (S_vars : Set (Fin N)), m_sa k)
    (⋂ j ∈ (S : Set (Fin m_count)), (E j)ᶜ) := by
    apply MeasurableSet.biInter S.countable_toSet
    intro j hj
    apply MeasurableSet.compl
    have h_sub : (B j : Set (Fin N)) ⊆ (S_vars : Set (Fin N)) :=
      fun k hk => Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨j, hj, hk⟩)
    exact (biSup_mono h_sub : (⨆ k ∈ (B j : Set (Fin N)), m_sa k) ≤ _) _ (hE_dep j)
  exact h_indep_sigma.indepSet_of_measurableSet hEi_meas h_avoid_meas

end LovaszLocalLemma

namespace LovaszLocalLemma

/--
[lll_bound_to_ennreal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/LLLRandomVariableModel.lean)
-/
@[path]
lemma lll_bound_to_ennreal
  {d : ℕ}
  {p : ℝ}
-- given
  (hLLL : rexp 1 * p * (↑d + 1) ≤ 1)
  (hp_nonneg : 0 ≤ p) :
-- imply
  ENNReal.ofReal (rexp 1) * ENNReal.ofReal p * (↑d + 1) ≤ 1 := by
-- proof
  have hd_cast : (↑d : ℝ≥0∞) + 1 = ENNReal.ofReal ((d : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg d) zero_le_one, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
  rw [hd_cast, ← ENNReal.ofReal_mul (le_of_lt (exp_pos 1)),
    ← ENNReal.ofReal_mul (mul_nonneg (le_of_lt (exp_pos 1)) hp_nonneg)]
  exact ENNReal.ofReal_le_one.mpr hLLL

end LovaszLocalLemma

namespace LovaszLocalLemma

/--
[lovasz_local_lemma_rv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/LLLRandomVariableModel.lean)
-/
@[path]
lemma lovasz_local_lemma_rv
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {N m : ℕ}
  {β : Fin N → Type*}
  [∀ j, MeasurableSpace (β j)]
  {X : (j : Fin N) → Ω → β j}
  {E : Fin m → Set Ω}
  {B : Fin m → Finset (Fin N)}
  {d : ℕ}
  {p : ℝ}
-- given
  (hX_indep : iIndepFun X μ)
  (hX_meas : ∀ j, Measurable (X j))
  (hE_meas : ∀ i, MeasurableSet (E i))
  (hE_dep : ∀ i, @MeasurableSet Ω (⨆ j ∈ B i, MeasurableSpace.comap (X j) inferInstance) (E i))
  (hd : ∀ i : Fin m, (Finset.univ.filter (fun j => j ≠ i ∧ (B i ∩ B j).Nonempty)).card ≤ d)
  (hp : ∀ i : Fin m, (μ (E i)).toReal ≤ p)
  (hLLL : Real.exp 1 * p * (↑d + 1) ≤ 1) :
-- imply
  0 < μ (⋂ i : Fin m, (E i)ᶜ) := by
-- proof
  classical
  set N_dep : Fin m → Finset (Fin m) :=
    fun i => Finset.univ.filter (fun j => j ≠ i ∧ (B i ∩ B j).Nonempty)
  obtain hm_zero | hm_pos := Nat.eq_zero_or_pos m
  · subst hm_zero
    simp [Set.iInter_of_empty, measure_univ]
  have hp_nonneg : 0 ≤ p :=
    le_trans ENNReal.toReal_nonneg (hp ⟨0, hm_pos⟩)
  apply LopsidedLLL.lopsided_local_lemma_symmetric E hE_meas N_dep
  ·
    intro i S hS
    have h_disj : ∀ j ∈ S, Disjoint (B i : Set (Fin N)) (B j : Set (Fin N)) := by
      intro j hj
      have hjmem := hS hj
      simp only [N_dep, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_union, Finset.mem_filter, Finset.mem_singleton, not_or, not_and] at hjmem
      obtain ⟨hj_not_dep, hj_ne_i⟩ := hjmem
      have h_empty : B i ∩ B j = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp (hj_not_dep hj_ne_i)
      exact Finset.disjoint_coe.mpr (Finset.disjoint_iff_inter_eq_empty.mpr h_empty)
    have h_indep := indepSet_of_disjoint_support hX_indep hX_meas hE_dep i S h_disj
    show μ[E i | LopsidedLLL.avoidSet E S] ≤ μ (E i)
    have h_eq : LopsidedLLL.avoidSet E S = ⋂ j ∈ (S : Set (Fin m)), (E j)ᶜ := by
      simp [LopsidedLLL.avoidSet]
    rwa [h_eq]
      (MeasurableSet.biInter S.countable_toSet (fun j _ => (hE_meas j).compl)) h_indep
  ·
    exact fun i => hd i
  ·
    intro i
    calc μ (E i) = ENNReal.ofReal (μ (E i)).toReal :=
      (ENNReal.ofReal_toReal (measure_ne_top μ (E i))).symm
      _ ≤ ENNReal.ofReal p := ENNReal.ofReal_le_ofReal (hp i)
  ·
    exact lll_bound_to_ennreal hLLL hp_nonneg

end LovaszLocalLemma


-- created on 2026-10-23
