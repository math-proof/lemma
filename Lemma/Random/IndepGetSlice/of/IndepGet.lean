import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Lemma.Random.CondIndepJoint.of.Indep_Joint.Indep
import sympy.stats.joint_rv
open ProbabilityTheory MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {r : ℕ → Ω → α} {s : ℕ → Ω → β}
-- given
  (hr : ∀ n, Measurable (r n))
  (hs : ∀ n, Measurable (s n))
  (h : ∀ t : ℕ, r t ⟂ᵢ[π]
    fun (ω : Ω) (i : Fin t) ↦ (s i, r i) ω) :
-- imply
  ∀ (t k : ℕ),
    (fun (ω : Ω) (i : Fin k) ↦ r (t + i.val) ω) ⟂ᵢ[π]
      (fun (ω : Ω) (i : Fin t) ↦ s i ω) := by
  intro t k
  let s_past (n : ℕ) : Ω → Fin n → β := fun ω i => s i ω
  let r_past (n : ℕ) : Ω → Fin n → α := fun ω i => r i ω
  let r_slice (start len : ℕ) : Ω → Fin len → α := fun ω j => r (start + j.val) ω
  induction k with
  | zero =>
    have hconst : (fun (ω : Ω) (i : Fin 0) ↦ r (t + i.val) ω) =
        (fun _ : Ω ↦ Fin.elim0 (α := α)) := by
      funext ω i
      cases i
      omega
    rw [hconst]
    exact indepFun_const_left (c := Fin.elim0 (α := α)) (X := fun (ω : Ω) (i : Fin t) ↦ s i ω)
  | succ k ih =>
    let proj : (Fin (t+k) → β × α) → ((Fin t → β) × (Fin k → α)) :=
      fun f => (fun i : Fin t => (f (Fin.castLE (by linarith) i)).1,
                fun j : Fin k => (f (Fin.natAdd t j)).2)
    have hproj : Measurable proj := by
      refine Measurable.prodMk ?_ ?_
      · refine measurable_pi_lambda _ ?_
        intro i
        show Measurable (fun f : Fin (t+k) → β × α => (f (Fin.castLE (by linarith) i)).1)
        exact measurable_fst.comp (measurable_pi_apply _)
      · refine measurable_pi_lambda _ ?_
        intro j
        show Measurable (fun f : Fin (t+k) → β × α => (f (Fin.natAdd t j)).2)
        exact measurable_snd.comp (measurable_pi_apply _)
    have heq_proj : ((s_past t, r_slice t k)) =
        proj ∘ (fun ω i => (s i, r i) ω) := by
      funext ω
      show (s_past t ω, r_slice t k ω) = proj (fun i : Fin (t+k) => (s i, r i) ω)
      have hs : (proj (fun i : Fin (t+k) => (s i, r i) ω)).1 = s_past t ω := by
        funext i
        simp [proj, JointRandomSymbol, Fin.castLE, s_past]
      have hr : (proj (fun i : Fin (t+k) => (s i, r i) ω)).2 = r_slice t k ω := by
        funext j
        simp [proj, JointRandomSymbol, Fin.natAdd, r_slice]
      exact Prod.ext hs hr
    have step_a : r (t+k) ⟂ᵢ[π] (s_past t, r_slice t k) := by
      show r (t+k) ⟂ᵢ[π] (s_past t, r_slice t k)
      rw [heq_proj]
      exact (h (t+k)).comp measurable_id hproj
    have hr_tk : Measurable (r (t + k)) := hr (t + k)
    have hs_past_m : Measurable (s_past t) := measurable_pi_lambda _ fun i => hs i.val
    have hr_slice_m : Measurable (r_slice t k) :=
      measurable_pi_lambda _ fun j => hr (t + j.val)
    have step_a' : r (t + k) ⟂ᵢ[π] (r_slice t k, s_past t) :=
      step_a.comp measurable_id measurable_swap
    have step_b : (r (t + k), r_slice t k) ⟂ᵢ[π] s_past t :=
      Random.CondIndepJoint.of.Indep_Joint.Indep hr_tk hr_slice_m hs_past_m step_a' ih
    let g : α × (Fin k → α) → Fin (k + 1) → α := fun p => @Fin.snoc k (fun _ => α) p.2 p.1
    have hg : Measurable g := by
      refine measurable_pi_lambda _ fun i => ?_
      change Measurable (fun p : α × (Fin k → α) => @Fin.snoc k (fun _ => α) p.2 p.1 i)
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]; exact measurable_fst
      · simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply j).comp measurable_snd
    have heq_snoc :
        r_slice t (k + 1) = g ∘ (r (t + k), r_slice t k) := by
      funext ω i
      change r (t + i.val) ω = @Fin.snoc k (fun _ => α) (r_slice t k ω) (r (t + k) ω) i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [r_slice, Fin.snoc_last, Fin.val_last]
      · simp [r_slice, Fin.snoc_castSucc, Fin.val_castSucc]
    show r_slice t (k + 1) ⟂ᵢ[π] s_past t
    rw [heq_snoc]
    exact step_b.comp hg measurable_id


-- created on 2023-04-01
