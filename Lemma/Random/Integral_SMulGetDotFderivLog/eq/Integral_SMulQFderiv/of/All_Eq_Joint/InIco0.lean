import Lemma.Random.Integral_SMul.of.In_Ico
import Lemma.Random.PSpace_Path.of.All_PSpace
import Lemma.Random.SinglePSpace.of.EqMeasureCount.Measurable
import Lemma.Random.Measurable_G.of.All_Measurable
import Lemma.Measure.Count.eq.ProdCountS
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import sympy.core.function
import sympy.vector.operators
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Filter Topology Measure
open scoped ENNReal.ToRealCoe
set_option maxHeartbeats 4000000


/--
`𝔼[∇ log π(a[t] | s[t]) • (γ ** Stack[k](k) @ r[t:])] =
  𝔼[∇ log π(a[t] | s[t]) • 𝔼[(γ ** Stack[k](k) @ r[t:]) | s[t], a[t]]]`
(law of iterated expectation on `(s[t], a[t])`).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t)) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable
      ((Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).prodMk
        (Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t))
      (by
        show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
        rw [CountableMeasure.measure_eq_count, CountableMeasure.measure_eq_count, Count.eq.ProdCountS])
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun _θ =>
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  𝔼[r, s, a : M θ](((γ ^ (id : ℕ → ℕ)) @ r[t:]) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) =
    𝔼[s, a : M θ](
      𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s[t], a[t]) •
        ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) := by
-- proof
  intro hP _ _ _ _
  classical
  rcases r with ⟨r⟩
  rcases s with ⟨s⟩
  rcases a with ⟨a⟩
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let _ : MeasurableSpace Θ := borel Θ
  have : ∀ t'', SinglePSpace (M θ) (a t'', s t'') := fun t'' => hP θ t''
  let ψ : S → A → Θ := fun x u =>
    ∇[θ] (ℙ[M θ]((a t) = u | (s t) = x) : ℝ).log
  have hsa : Measurable fun p : (ℕ → S) × (ℕ → A) ↦ (p.1 t, p.2 t) :=
    ((measurable_pi_apply t).comp measurable_fst).prodMk
      ((measurable_pi_apply t).comp measurable_snd)
  have hsa3 : Measurable fun p : (ℕ → ℝ) × ((ℕ → S) × (ℕ → A)) ↦ (p.2.1 t, p.2.2 t) :=
    ((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd))
  have hGpath : StronglyMeasurable fun p : (ℕ → ℝ) × ((ℕ → S) × (ℕ → A)) ↦
      ((γ ^ (id : ℕ → ℕ)) @ fun k ↦ p.1 (t + k)) :=
    (Measurable_G.of.All_Measurable
      (r := fun j (p : (ℕ → ℝ) × ((ℕ → S) × (ℕ → A))) => p.1 j)
      (fun j => (measurable_pi_apply j).comp measurable_fst) γ t).stronglyMeasurable
  have hψpath3 : StronglyMeasurable fun p : (ℕ → ℝ) × ((ℕ → S) × (ℕ → A)) ↦
      ψ (p.2.1 t) (p.2.2 t) :=
    StronglyMeasurable.comp_measurable
      (f := fun q : S × A ↦ ψ q.1 q.2) StronglyMeasurable.of_discrete hsa3
  have hQpath : StronglyMeasurable fun p : (ℕ → S) × (ℕ → A) ↦
      𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = p.1 t ∧ a t = p.2 t) :=
    ((measurable_of_countable fun q : S × A =>
        𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = q.1 ∧ a t = q.2)).comp hsa).stronglyMeasurable
  have hψpath2 : StronglyMeasurable fun p : (ℕ → S) × (ℕ → A) ↦ ψ (p.1 t) (p.2 t) :=
    StronglyMeasurable.comp_measurable
      (f := fun q : S × A ↦ ψ q.1 q.2) StronglyMeasurable.of_discrete hsa
  have hL :
      𝔼[r, s, a : M θ](((γ ^ (id : ℕ → ℕ)) @ r[t:]) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) =
        ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω • ψ (s t ω) (a t ω) ∂(M θ) := by
    rw [Expectation.ofRV, expectation_bochner]
    have hx : AEMeasurable
        (JointRandomSymbol (Expectation.asRV r)
          (JointRandomSymbol (Expectation.asRV s) (Expectation.asRV a))) (M θ) :=
      PSpace.aemeasurable
    refine (integral_map hx (hGpath.smul hψpath3).aestronglyMeasurable).trans ?_
    simp only [JointRandomSymbol, AsPathRV.path_process]
    rfl
  have hcore :
      ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω • ψ (s t ω) (a t ω) ∂(M θ) =
        ∫ ω, 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = s t ω ∧ a t = a t ω) •
          ψ (s t ω) (a t ω) ∂(M θ) := by
    convert Integral_SMul.of.In_Ico (M := M) h₀ h₁ θ t ψ using 1
  refine hL.trans (hcore.trans ?_)
  symm
  rw [Expectation.ofRV, expectation_bochner]
  have hx : AEMeasurable (AsPathRV.path s, AsPathRV.path a) (M θ) :=
    PSpace.aemeasurable
  refine (integral_map hx (hQpath.smul hψpath2).aestronglyMeasurable).trans ?_
  simp only [JointRandomSymbol, AsPathRV.path_process]
  -- RHS GetElem score matches ψ after observation unwrap
  rfl


-- created on 2023-04-01
-- updated on 2026-10-20
