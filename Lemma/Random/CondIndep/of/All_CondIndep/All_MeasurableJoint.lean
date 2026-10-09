import sympy.stats.joint_rv
import sympy.vector.Basic
import sympy.stats.hidden_markov_sequence
import Lemma.Measure.CondIndep.of.CondIndep.CondIndep.Le_M.Le_M.Le_M
import Lemma.Measure.CondIndep.of.Le.Le.CondIndep.Le_M.Le_M.Le_M.Le_M
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory


/--
Future irrelevance from the one-step Markov property (history irrelevance) of a Markov decision process.
-/
@[path]
private lemma main
  [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace S] [MeasurableSpace A]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ → Ω → S}
  {a : ℕ → Ω → A}
  {r : ℕ → Ω → ℝ}
  {t : ℕ}
-- given
  (h₀ : ∀ t, Measurable (r t, s t, a t))
  (h₁ : ∀ n, (a n, r n, s (n + 1)) ⟂ᵢ[π] (r, s, a)[:n] | s n) :
-- imply
  r[t + 1:] ⟂ᵢ[π] (s t, a t) | s (t + 1) := by
-- proof
  have hrm : ∀ n, Measurable (r n) := fun n ↦ (h₀ n).fst
  have hsm : ∀ n, Measurable (s n) := fun n ↦ (h₀ n).snd.fst
  have ham : ∀ n, Measurable (a n) := fun n ↦ (h₀ n).snd.snd
  -- the step `X m = (a m, r m, s (m + 1))` and the history `H n = ((r i, s i, a i))_{i < n}`
  let X : ℕ → Ω → A × ℝ × S := fun m ω ↦ (a m ω, r m ω, s (m + 1) ω)
  let H : (n : ℕ) → Ω → Fin n → ℝ × S × A := fun n ω i ↦ (r i ω, s i ω, a i ω)
  have hXm : ∀ m, Measurable (X m) := fun m ↦ (ham m).prodMk ((hrm m).prodMk (hsm (m + 1)))
  have hHm : ∀ n, Measurable (H n) := fun n ↦
    Measurable.of_eval fun i ↦ (hrm i).prodMk ((hsm i).prodMk (ham i))
  have hM : ∀ n, ProbabilityTheory.CondIndep (MeasurableSpace.comap (s n) inferInstance) (MeasurableSpace.comap (X n) inferInstance)
      (MeasurableSpace.comap (H n) inferInstance) (hsm n).comap_le π := fun n ↦ h₁ n
  -- σ-algebras
  let Y : ℕ → MeasurableSpace Ω := fun k ↦ ⨆ j < k, MeasurableSpace.comap (X (t + 1 + j)) inferInstance
  have hG : (MeasurableSpace.comap (s (t + 1)) inferInstance) ≤ mΩ := (hsm (t + 1)).comap_le
  have hHσ : (MeasurableSpace.comap (H (t + 1)) inferInstance) ≤ mΩ := (hHm (t + 1)).comap_le
  have hY : ∀ k, Y k ≤ mΩ := fun k ↦ iSup₂_le fun j _ ↦ (hXm (t + 1 + j)).comap_le
  -- measurability w.r.t. `σ(s m) ⊔ σ(H m)` of everything up to time `m`
  have hR : ∀ m, MeasurableSpace.comap (s m) inferInstance ⊔ MeasurableSpace.comap (H m) inferInstance ≤ mΩ :=
    fun m ↦ sup_le (hsm m).comap_le (hHm m).comap_le
  have hpast : ∀ m i (hi : i < m), Measurable[MeasurableSpace.comap (s m) inferInstance ⊔ MeasurableSpace.comap (H m) inferInstance]
      (fun ω ↦ H m ω ⟨i, hi⟩) := fun m i hi ↦
    ((measurable_pi_apply _).comp (comap_measurable (H m))).mono le_sup_right le_rfl
  have hsR : ∀ m i, i ≤ m →
      Measurable[MeasurableSpace.comap (s m) inferInstance ⊔ MeasurableSpace.comap (H m) inferInstance] (s i) := by
    intro m i hi
    rcases hi.lt_or_eq with hi | rfl
    · exact measurable_fst.comp (measurable_snd.comp (hpast m i hi))
    · exact (comap_measurable (s i)).mono le_sup_left le_rfl
  have hrR : ∀ m i, i < m →
      Measurable[MeasurableSpace.comap (s m) inferInstance ⊔ MeasurableSpace.comap (H m) inferInstance] (r i) :=
    fun m i hi ↦ measurable_fst.comp (hpast m i hi)
  have haR : ∀ m i, i < m →
      Measurable[MeasurableSpace.comap (s m) inferInstance ⊔ MeasurableSpace.comap (H m) inferInstance] (a i) :=
    fun m i hi ↦ measurable_snd.comp (measurable_snd.comp (hpast m i hi))
  -- `Y k` is conditionally independent of the history given `s (t + 1)`
  have P : ∀ k, ProbabilityTheory.CondIndep (MeasurableSpace.comap (s (t + 1)) inferInstance) (MeasurableSpace.comap (H (t + 1)) inferInstance) (Y k) hG π := by
    intro k
    induction k with
    | zero =>
      have : Y 0 = ⊥ := by simp [Y]
      rw [this]
      exact condIndep_bot_right _
    | succ k ih =>
      have hYs : Y (k + 1) = Y k ⊔ MeasurableSpace.comap (X (t + 1 + k)) inferInstance :=
        Nat.iSup_lt_succ (fun j ↦ MeasurableSpace.comap (X (t + 1 + j)) inferInstance) k
      rw [hYs]
      refine Measure.CondIndep.of.CondIndep.CondIndep.Le_M.Le_M.Le_M hHσ (hY k) (hXm _).comap_le ih ?_
      refine (Measure.CondIndep.of.Le.Le.CondIndep.Le_M.Le_M.Le_M.Le_M (hXm _).comap_le (hHm _).comap_le (sup_le hG (hY k)) hHσ (hM (t + 1 + k)) ?_ ?_).symm
      · -- `σ(s (t + 1 + k)) ≤ σ(s (t + 1)) ⊔ Y k`
        rcases k with _ | k
        · exact le_sup_left
        · refine le_sup_of_le_right (le_iSup₂_of_le k (Nat.lt_succ_self k) ?_)
          exact measurable_iff_comap_le.1 (measurable_snd.comp (measurable_snd.comp (comap_measurable (X (t + 1 + k)))))
      · refine sup_le (sup_le ?_ ?_) ?_
        · exact measurable_iff_comap_le.1 (hsR _ _ (by omega))
        · refine iSup₂_le fun j hj ↦ measurable_iff_comap_le.1 ?_
          exact (haR _ _ (by omega)).prodMk ((hrR _ _ (by omega)).prodMk (hsR _ _ (by omega)))
        · refine measurable_iff_comap_le.1
            (@Measurable.of_eval Ω _ _
              (MeasurableSpace.comap (s (t + 1 + k)) inferInstance ⊔
                MeasurableSpace.comap (H (t + 1 + k)) inferInstance)
              _ _ fun i ↦ ?_)
          have hi := i.isLt
          exact (hrR _ _ (by omega)).prodMk ((hsR _ _ (by omega)).prodMk (haR _ _ (by omega)))
  -- pass to the whole future
  have hmono : Monotone Y := fun k k' hk ↦
    iSup₂_le fun j hj ↦ le_iSup₂_of_le (f := fun j (_ : j < k') ↦ MeasurableSpace.comap (X (t + 1 + j)) inferInstance)
      j (lt_of_lt_of_le hj hk) le_rfl
  have hsupY := condIndep_iSup_of_directed_le (fun k ↦ (P k).symm) hY hHσ hmono.directed_le
  refine condIndep_of_condIndep_of_le_right (condIndep_of_condIndep_of_le_left hsupY ?_) ?_
  · refine measurable_iff_comap_le.1
      (@Measurable.of_eval Ω _ _ (⨆ k, Y k) _ _ fun k ↦ ?_)
    have h1 : Measurable[Y (k + 1)] (r (t + 1 + k)) :=
      (measurable_fst.comp (measurable_snd.comp (comap_measurable (X (t + 1 + k))))).mono
        (le_iSup₂_of_le (f := fun j (_ : j < k + 1) ↦ MeasurableSpace.comap (X (t + 1 + j)) inferInstance)
          k (Nat.lt_succ_self k) le_rfl) le_rfl
    exact h1.mono (le_iSup Y (k + 1)) le_rfl
  · refine measurable_iff_comap_le.1 ?_
    have hp : Measurable[(MeasurableSpace.comap (H (t + 1)) inferInstance)] (fun ω ↦ H (t + 1) ω ⟨t, Nat.lt_succ_self t⟩) :=
      (measurable_pi_apply _).comp (comap_measurable (H (t + 1)))
    exact (measurable_fst.comp (measurable_snd.comp hp)).prodMk
      (measurable_snd.comp (measurable_snd.comp hp))


-- created on 2026-10-06
