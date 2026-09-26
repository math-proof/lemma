import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Lemma.Random.CondIndepJoint.of.Indep_Joint.Indep
import sympy.stats.joint_rv
open ProbabilityTheory MeasureTheory Random


/--
Joint history-irrelevance: if the reward `r t` is independent of the preceding
action-state-reward history at every time, then every finite slice of the future
reward stream starting at `t + 1` is independent of the current state-action pair
`(s t, a t)`.

Python: Random.EqConditioned.of.Eq_Conditioned.joint.independence_assumption.
-/
@[main]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {r : ℕ → Ω → α} {s : ℕ → Ω → β} {a : ℕ → Ω → γ}
-- given
  (hr : ∀ n, Measurable (r n))
  (hs : ∀ n, Measurable (s n))
  (ha : ∀ n, Measurable (a n))
  (h : ∀ t : ℕ, r t ⟂ᵢ[π]
    fun (ω : Ω) (i : Fin t) ↦ ((a i, s i), r i) ω) :
-- imply
  ∀ (t k : ℕ),
    (fun (ω : Ω) (i : Fin k) ↦ r (t + 1 + i.val) ω) ⟂ᵢ[π] (s t, a t) := by
-- proof
  intro t k
  let as_past (n : ℕ) : Ω → Fin n → γ × β :=
    fun ω i ↦ (a i ω, s i ω)
  let r_slice (start len : ℕ) : Ω → Fin len → α :=
    fun ω j ↦ r (start + j.val) ω
  have h_slice : ∀ k : ℕ, r_slice (t + 1) k ⟂ᵢ[π] as_past (t + 1) := by
    intro k
    induction k with
    | zero =>
      have hconst : r_slice (t + 1) 0 = fun _ : Ω ↦ Fin.elim0 (α := α) := by
        funext ω i
        cases i
        omega
      rw [hconst]
      exact indepFun_const_left (c := Fin.elim0 (α := α))
        (X := as_past (t + 1))
    | succ k ih =>
      let proj : (Fin (t + 1 + k) → (γ × β) × α) →
          (Fin (t + 1) → γ × β) × (Fin k → α) :=
        fun f ↦
          (fun i : Fin (t + 1) ↦
            (f (Fin.castLE (by linarith) i)).1,
           fun j : Fin k ↦ (f (Fin.natAdd (t + 1) j)).2)
      have hproj : Measurable proj := by
        refine Measurable.prodMk ?_ ?_
        · refine measurable_pi_lambda _ fun i ↦
            measurable_fst.comp (measurable_pi_apply (Fin.castLE (by linarith) i))
        · refine measurable_pi_lambda _ fun j ↦
            measurable_snd.comp (measurable_pi_apply (Fin.natAdd (t + 1) j))
      have hstep : r (t + 1 + k) ⟂ᵢ[π] (as_past (t + 1), r_slice (t + 1) k) :=
        (h (t + 1 + k)).comp measurable_id hproj
      have h_mr : Measurable (r (t + 1 + k)) := hr (t + 1 + k)
      have h_slice_m : Measurable (r_slice (t + 1) k) :=
        measurable_pi_lambda _ fun j ↦ hr (t + 1 + j.val)
      have h_as_m : Measurable (as_past (t + 1)) :=
        measurable_pi_lambda _ fun i ↦ (ha i.val).prodMk (hs i.val)
      have hstep' : r (t + 1 + k) ⟂ᵢ[π] (r_slice (t + 1) k, as_past (t + 1)) :=
        hstep.comp measurable_id measurable_swap
      have hcombine :
          (r (t + 1 + k), r_slice (t + 1) k) ⟂ᵢ[π] as_past (t + 1) :=
        CondIndepJoint.of.Indep_Joint.Indep h_mr h_slice_m h_as_m hstep' ih
      let g : α × (Fin k → α) → Fin (k + 1) → α :=
        fun p ↦ @Fin.snoc k (fun _ ↦ α) p.2 p.1
      have hg : Measurable g := by
        refine measurable_pi_lambda _ fun i ↦ ?_
        change Measurable (fun p : α × (Fin k → α) ↦
          @Fin.snoc k (fun _ ↦ α) p.2 p.1 i)
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simp only [Fin.snoc_last]; exact measurable_fst
        · simp only [Fin.snoc_castSucc]
          exact (measurable_pi_apply j).comp measurable_snd
      have heq_snoc :
          r_slice (t + 1) (k + 1) = g ∘ (r (t + 1 + k), r_slice (t + 1) k) := by
        funext ω i
        change r (t + 1 + i.val) ω =
          @Fin.snoc k (fun _ ↦ α) (r_slice (t + 1) k ω) (r (t + 1 + k) ω) i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simp [r_slice, Fin.snoc_last, Fin.val_last]
        · simp [r_slice, Fin.snoc_castSucc, Fin.val_castSucc]
      rw [heq_snoc]
      exact hcombine.comp hg measurable_id
  let i_last : Fin (t + 1) := ⟨t, by omega⟩
  let cur : (Fin (t + 1) → γ × β) → β × γ :=
    fun f ↦ ((f i_last).2, (f i_last).1)
  have hcur : Measurable cur :=
    (measurable_snd.comp (measurable_pi_apply i_last)).prodMk
      (measurable_fst.comp (measurable_pi_apply i_last))
  have heq_cur : (s t, a t) = cur ∘ as_past (t + 1) := by
    funext ω
    simp [cur, as_past, i_last, JointRandomSymbol]
  rw [heq_cur]
  exact (h_slice k).comp measurable_id hcur


-- created on 2026-09-26
