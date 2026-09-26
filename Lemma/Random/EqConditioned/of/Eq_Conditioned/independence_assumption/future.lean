import Lemma.Random.IndepGetSlice.of.IndepGet
import sympy.stats.joint_rv
open ProbabilityTheory MeasureTheory Random


/--
History-irrelevant rewards (each reward is independent of the preceding
state-reward history) imply that every finite slice of the future reward stream
starting at `t + 1` is independent of the current state `s t`.

Python: Random.EqConditioned.of.Eq_Conditioned.independence_assumption.future.
-/
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
    (fun (ω : Ω) (i : Fin k) ↦ r (t + 1 + i.val) ω) ⟂ᵢ[π] s t := by
-- proof
  intro t k
  let s_past (n : ℕ) : Ω → Fin n → β := fun ω i ↦ s i ω
  let r_slice (start len : ℕ) : Ω → Fin len → α :=
    fun ω j ↦ r (start + j.val) ω
  let i_last : Fin (t + 1) := ⟨t, by omega⟩
  let unsnoc : (Fin (t + 1) → β) → (Fin t → β) × β := fun f ↦
    (fun i : Fin t ↦ f i.castSucc, f i_last)
  have hunsnoc : Measurable unsnoc :=
    (measurable_pi_lambda _ fun i ↦ measurable_pi_apply i.castSucc).prodMk
      (measurable_pi_apply i_last)
  have h_eq :
      JointRandomSymbol (s_past t) (s t) = unsnoc ∘ s_past (t + 1) := by
    funext ω
    simp only [unsnoc, JointRandomSymbol, s_past]
    rfl
  have h1 : r_slice (t + 1) k ⟂ᵢ[π] s_past (t + 1) :=
    IndepGetSlice.of.IndepGet hr hs h (t + 1) k
  have h2 : r_slice (t + 1) k ⟂ᵢ[π] JointRandomSymbol (s_past t) (s t) := by
    rw [h_eq]
    exact h1.comp measurable_id hunsnoc
  exact h2.comp measurable_id measurable_snd


-- created on 2026-09-26
