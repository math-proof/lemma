import sympy.stats.joint_rv
import sympy.Basic
open ProbabilityTheory MeasureTheory


/--
History-irrelevant conditional independence (the RL "future reward is independent of
past states" assumption, a.k.a. the premise `IndepGet`): if the reward `r t` is
independent of the state history `s 0, …, s (t-1)` at **every** time `t`, then the
reward at any later time `r (t + k)` is still independent of the same history `s 0, …, s (t-1)`.
-/
@[main]
private lemma main
  {Ω α β : Type*}
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : Measure Ω}
  {r : ℕ → Ω → α} {s : ℕ → Ω → β}
-- given
  (h : ∀ t : ℕ, r t ⟂ᵢ[π] (fun (ω : Ω) (i : Fin t) ↦ s i ω)) :
-- imply
  ∀ (t k : ℕ), r (t + k) ⟂ᵢ[π] (fun (ω : Ω) (i : Fin t) ↦ s i ω) := by
-- proof
  intro t k
  have htk : r (t + k) ⟂ᵢ[π] (fun (ω : Ω) (i : Fin (t + k)) ↦ s i ω) := h (t + k)
  let restrict : (Fin (t + k) → β) → (Fin t → β) :=
    fun f i ↦ f (Fin.castLE (by linarith) i)
  have hres : Measurable restrict := by
    rw [measurable_pi_iff]
    intro i
    simpa [restrict] using measurable_pi_apply (Fin.castLE (by linarith) i)
  have hcomp : (fun (ω : Ω) (i : Fin t) ↦ s i ω) =
      restrict ∘ (fun (ω : Ω) (i : Fin (t + k)) ↦ s i ω) := by
    funext ω i
    simp [restrict]
  rw [hcomp]
  exact htk.comp measurable_id hres


-- created on 2023-04-01
