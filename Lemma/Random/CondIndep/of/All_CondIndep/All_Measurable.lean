import sympy.stats.joint_rv
import sympy.stats.hidden_markov_sequence
import Lemma.Measure.CondIndep.of.CondIndep.CondIndep.Le_M.Le_M.Le_M
import Lemma.Measure.CondIndep.of.Le.Le.CondIndep.Le_M.Le_M.Le_M.Le_M
open MeasureTheory ProbabilityTheory Measure


/--
History irrelevance of the future rewards from the one-step Markov property of a Markov decision process:
if every step `(a n, r n, s (n + 1))` is conditionally independent of the history `(r, s, a)[:n]` given `s n`,
then the future reward path `r[t:]` is conditionally independent of the history `(r, s, a)[:t]` given the
current step `(s t, a t)`. This is the hypothesis of
`Random.MEqExpect.of.CondIndep.Integrable.Measurable.All_Measurable` (forgetting histories).
Proof: the whole future `σ(X t, X (t + 1), …)`, `X m = (a m, r m, s (m + 1))`, is conditionally independent of
the history given `s t` (contraction, by induction, then `condIndep_iSup_of_directed_le`); weak union then moves
`a t`, a component of `X t`, into the conditioning.
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
  r[t:] ⟂ᵢ[π] (r, s, a)[:t] | (s t, a t) := by
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
  have hM : ∀ n, ProbabilityTheory.CondIndep (MeasurableSpace.comap (s n) inferInstance)
    (MeasurableSpace.comap (X n) inferInstance) (MeasurableSpace.comap (H n) inferInstance) (hsm n).comap_le π :=
    fun n ↦ h₁ n
  -- σ-algebras
  let Y : ℕ → MeasurableSpace Ω := fun k ↦ ⨆ j < k, MeasurableSpace.comap (X (t + j)) inferInstance
  have hG : MeasurableSpace.comap (s t) inferInstance ≤ mΩ := (hsm t).comap_le
  have hHσ : MeasurableSpace.comap (H t) inferInstance ≤ mΩ := (hHm t).comap_le
  have hY : ∀ k, Y k ≤ mΩ := fun k ↦ iSup₂_le fun j _ ↦ (hXm (t + j)).comap_le
  -- measurability w.r.t. `σ(s m) ⊔ σ(H m)` of everything up to time `m`
  have hpast : ∀ m i (hi : i < m),
    Measurable[MeasurableSpace.comap (s m) inferInstance ⊔ MeasurableSpace.comap (H m) inferInstance]
      (fun ω ↦ H m ω ⟨i, hi⟩) := fun m i hi ↦
    ((measurable_pi_apply _).comp (comap_measurable (H m))).mono le_sup_right le_rfl
  have hsR : ∀ m i, i ≤ m →
    Measurable[MeasurableSpace.comap (s m) inferInstance ⊔ MeasurableSpace.comap (H m) inferInstance] (s i) := by
    intro m i hi
    obtain hi | rfl := hi.lt_or_eq
    · exact measurable_fst.comp (measurable_snd.comp (hpast m i hi))
    · exact (comap_measurable (s i)).mono le_sup_left le_rfl
  have hrR : ∀ m i, i < m →
    Measurable[MeasurableSpace.comap (s m) inferInstance ⊔ MeasurableSpace.comap (H m) inferInstance] (r i) :=
    fun m i hi ↦ measurable_fst.comp (hpast m i hi)
  have haR : ∀ m i, i < m →
    Measurable[MeasurableSpace.comap (s m) inferInstance ⊔ MeasurableSpace.comap (H m) inferInstance] (a i) :=
    fun m i hi ↦ measurable_snd.comp (measurable_snd.comp (hpast m i hi))
  -- `Y k` is conditionally independent of the history given `s t`
  have P : ∀ k, ProbabilityTheory.CondIndep (MeasurableSpace.comap (s t) inferInstance)
    (MeasurableSpace.comap (H t) inferInstance) (Y k) hG π := by
    intro k
    induction k with
    | zero =>
      have : Y 0 = ⊥ := by simp [Y]
      rw [this]
      exact condIndep_bot_right _
    | succ k ih =>
      have hYs : Y (k + 1) = Y k ⊔ MeasurableSpace.comap (X (t + k)) inferInstance :=
        Nat.iSup_lt_succ (fun j ↦ MeasurableSpace.comap (X (t + j)) inferInstance) k
      rw [hYs]
      refine CondIndep.of.CondIndep.CondIndep.Le_M.Le_M.Le_M hHσ (hY k) (hXm _).comap_le ih ?_
      refine (CondIndep.of.Le.Le.CondIndep.Le_M.Le_M.Le_M.Le_M (hXm _).comap_le (hHm _).comap_le
        (sup_le hG (hY k)) hHσ (hM (t + k)) ?_ ?_).symm
      · -- `σ(s (t + k)) ≤ σ(s t) ⊔ Y k`
        obtain _ | k := k
        · exact le_sup_left
        ·
          refine le_sup_of_le_right (le_iSup₂_of_le k (Nat.lt_succ_self k) ?_)
          exact measurable_iff_comap_le.1 (measurable_snd.comp (measurable_snd.comp (comap_measurable (X (t + k)))))
      ·
        refine sup_le (sup_le ?_ ?_) ?_
        · exact measurable_iff_comap_le.1 (hsR _ _ (by omega))
        ·
          refine iSup₂_le fun j hj ↦ measurable_iff_comap_le.1 ?_
          exact (haR _ _ (by omega)).prodMk ((hrR _ _ (by omega)).prodMk (hsR _ _ (by omega)))
        ·
          refine measurable_iff_comap_le.1
            (@Measurable.of_eval Ω _ _
              (MeasurableSpace.comap (s (t + k)) inferInstance ⊔
                MeasurableSpace.comap (H (t + k)) inferInstance)
              _ _ fun i ↦ ?_)
          have hi := i.isLt
          exact (hrR _ _ (by omega)).prodMk ((hsR _ _ (by omega)).prodMk (haR _ _ (by omega)))
  -- pass to the whole future
  have hmono : Monotone Y := fun k k' hk ↦
    iSup₂_le fun j hj ↦ le_iSup₂_of_le (f := fun j (_ : j < k') ↦ MeasurableSpace.comap (X (t + j)) inferInstance)
      j (lt_of_lt_of_le hj hk) le_rfl
  have hsupY := condIndep_iSup_of_directed_le (fun k ↦ (P k).symm) hY hHσ hmono.directed_le
  have hYsup : (⨆ k, Y k) ≤ mΩ := iSup_le hY
  -- the step `X (t + k)` belongs to the future, in particular `a t`
  have hX1 : ∀ k, Measurable[⨆ k, Y k] (X (t + k)) := fun k ↦
    (comap_measurable (X (t + k))).mono
      ((le_iSup₂_of_le (f := fun j (_ : j < k + 1) ↦ MeasurableSpace.comap (X (t + j)) inferInstance)
        k (Nat.lt_succ_self k) le_rfl).trans (le_iSup Y (k + 1))) le_rfl
  have hJ : Measurable (s t, a t) := (hsm t).prodMk (ham t)
  -- weak union: move `a t` into the conditioning
  have hW := CondIndep.of.Le.Le.CondIndep.Le_M.Le_M.Le_M.Le_M hHσ hYsup hJ.comap_le hYsup hsupY.symm ?_ ?_
  ·
    refine condIndep_of_condIndep_of_le_left hW.symm ?_
    exact measurable_iff_comap_le.1
      (@Measurable.of_eval Ω _ _ (⨆ k, Y k) _ _
        fun k ↦ measurable_fst.comp (measurable_snd.comp (hX1 k)))
  ·
    refine measurable_iff_comap_le.1 ?_
    exact measurable_fst.comp (comap_measurable (s t, a t))
  ·
    refine sup_le ?_ le_sup_right
    refine measurable_iff_comap_le.1 ?_
    have h0 := hX1 0
    simp only [add_zero] at h0
    exact ((comap_measurable (s t)).mono le_sup_left le_rfl).prodMk ((measurable_fst.comp h0).mono le_sup_right le_rfl)


/--
Forgetting histories (py `Random.EqProbSCond.of.CondIndep`):
`r[t:] | s[:t + 1] & a[:t + 1] = r[t:] | s[t] & a[t]`, i.e. given the current step `(s t, a t)`, the future
reward path `r[t:]` is conditionally independent of the state-action history `(s, a)[:t + 1]`.
The py hypothesis, history-irrelevant rewards `r[t] | s[:t] & a[:t] = r[t]` (plain independence), does not
suffice (counterexample: fair bits `a 0, a 1` and `r 1 = a 0 xor a 1`); it is replaced by the one-step Markov
property `h₁` of `main`.
Proof: (1) `main` gives `r[t:] ⟂ᵢ[π] (r, s, a)[:t] | (s t, a t)`;
(2) `(s, a)[:t + 1]` is a measurable function of `(r, s, a)[:t]` and `(s t, a t)`; (3) weak union.
-/
@[path]
private lemma forget_history
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
  r[t:] ⟂ᵢ[π] (s, a)[:t + 1] | (s t, a t) := by
-- proof
  -- step 1: the Markov property makes the future rewards independent of the whole history given the current step
  have h₂ : r[t:] ⟂ᵢ[π] (r, s, a)[:t] | (s t, a t) := main h₀ h₁
  -- step 2: the state-action history `(s, a)[:t + 1]` is a function of the history `(r, s, a)[:t]` and the current step `(s t, a t)`
  have h₃ : MeasurableSpace.comap ((s, a)[:t + 1]) inferInstance ≤ MeasurableSpace.comap (s t, a t) inferInstance ⊔ MeasurableSpace.comap ((r, s, a)[:t]) inferInstance := by
    refine measurable_iff_comap_le.1
      (@Measurable.of_eval Ω _ _
        (MeasurableSpace.comap (s t, a t) inferInstance ⊔
          MeasurableSpace.comap ((r, s, a)[:t]) inferInstance)
        _ _ fun i ↦ ?_)
    obtain ⟨i, hi⟩ := i
    obtain hi | rfl := Nat.lt_succ_iff_lt_or_eq.mp hi
    ·
      apply (measurable_snd.comp ((measurable_pi_apply ⟨i, hi⟩).comp (comap_measurable ((r, s, a)[:t])))).mono le_sup_right le_rfl
    ·
      apply (comap_measurable (s i, a i)).mono le_sup_left le_rfl
  -- step 3: weak union, shrinking the history `(r, s, a)[:t]` to `(s, a)[:t + 1]`
  apply CondIndep.of.Le.Le.CondIndep.Le_M.Le_M.Le_M.Le_M _ _ _ _ h₂ le_rfl
  exact sup_le le_sup_left h₃
  apply Measurable.comap_le (Measurable.of_eval fun k ↦ (h₀ (t + k)).fst)
  apply Measurable.comap_le (Measurable.of_eval fun (i : Fin t) ↦ h₀ i)
  apply Measurable.comap_le (Measurable.of_eval fun (i : Fin (t + 1)) ↦ (h₀ i).snd)


-- created on 2026-10-07
