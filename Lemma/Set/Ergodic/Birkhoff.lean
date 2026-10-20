import Mathlib
import sympy.Basic
import sympy.atlas.Dynamics.Ergodic.Birkhoff
open MeasureTheory
open MathlibExt.Dynamics.Ergodic.BirkhoffWanted


/--
[maximal_ergodic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Ergodic/Birkhoff.lean)
-/
@[path]
private lemma maximal_ergodic_eq
  [MeasurableSpace α]
  {μ : Measure α} [IsFiniteMeasure μ]
  {T : α → α}
  {f : α → ℝ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hf : Measurable f)
  (hfi : Integrable f μ) :
-- imply
  0 ≤ ∫ x in {x | ∃ n, 0 < birkhoffSum T f n x}, f x ∂μ := by
-- proof
  apply MathlibExt.Dynamics.Ergodic.BirkhoffWanted.maximal_ergodic hT hf hfi

/--
[dick_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Ergodic/Birkhoff.lean)
-/
@[path]
private lemma dick_measurable_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {g : α → ℝ}
  {c : ℝ}
-- given
  (hT : MeasurePreserving T μ μ)
  (hg : Measurable g) :
-- imply
  MeasurableSet (DickSet T g c) := by
-- proof
  apply MathlibExt.Dynamics.Ergodic.BirkhoffWanted.dick_measurable hT hg c

/--
[dick_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Ergodic/Birkhoff.lean)
-/
@[path]
private lemma dick_mem_eq
  [MeasurableSpace α]
  {T : α → α}
  {g : α → ℝ}
  {c : ℝ}
  {x : α} :
-- imply
  x ∈ DickSet T g c ↔ ∃ q : ℚ, c < (q : ℝ) ∧
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (n : ℝ) * (q : ℝ) < birkhoffSum T g n x := by
-- proof
  apply MathlibExt.Dynamics.Ergodic.BirkhoffWanted.dick_mem

/--
[dick_inv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Ergodic/Birkhoff.lean)
-/
@[path]
private lemma dick_inv_eq
  [MeasurableSpace α]
  {T : α → α}
  {g : α → ℝ}
  {c : ℝ} :
-- imply
  T ⁻¹' DickSet T g c = DickSet T g c := by
-- proof
  apply MathlibExt.Dynamics.Ergodic.BirkhoffWanted.dick_inv

/--
[dick_iter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Ergodic/Birkhoff.lean)
-/
@[path]
private lemma dick_iter_eq
  [MeasurableSpace α]
  {T : α → α}
  {g : α → ℝ}
  {c : ℝ}
  {k : ℕ}
  {x : α} :
-- imply
  (T^[k] x ∈ DickSet T g c) ↔ (x ∈ DickSet T g c) := by
-- proof
  apply MathlibExt.Dynamics.Ergodic.BirkhoffWanted.dick_iter k x

/--
[dick_sum_in](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Ergodic/Birkhoff.lean)
-/
@[path]
private lemma dick_sum_in_eq
  [MeasurableSpace α]
  {T : α → α}
  {g : α → ℝ}
  {c : ℝ}
  {D : Set α}
  {x : α}
  {n : ℕ}
-- given
  (hiter : ∀ (k : ℕ) (x : α), (T^[k] x ∈ D) ↔ (x ∈ D))
  (hfun : α → ℝ)
  (hfundef : ∀ y : α, hfun y = D.indicator (fun y => g y - c) y)
  (hx : x ∈ D) :
-- imply
  birkhoffSum T hfun n x = birkhoffSum T g n x - n * c := by
-- proof
  apply MathlibExt.Dynamics.Ergodic.BirkhoffWanted.dick_sum_in D hiter hfun hfundef x hx n

/--
[dick_sum_out](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Ergodic/Birkhoff.lean)
-/
@[path]
private lemma dick_sum_out_eq
  [MeasurableSpace α]
  {T : α → α}
  {g : α → ℝ}
  {c : ℝ}
  {D : Set α}
  {x : α}
  {n : ℕ}
-- given
  (hiter : ∀ (k : ℕ) (x : α), (T^[k] x ∈ D) ↔ (x ∈ D))
  (hfun : α → ℝ)
  (hfundef : ∀ y : α, hfun y = D.indicator (fun y => g y - c) y)
  (hx : x ∉ D) :
-- imply
  birkhoffSum T hfun n x = 0 := by
-- proof
  apply MathlibExt.Dynamics.Ergodic.BirkhoffWanted.dick_sum_out D hiter hfun hfundef x hx n

/--
[birkhoff_pointwise_ergodic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Ergodic/Birkhoff.lean)
-/
@[path]
private lemma birkhoff_pointwise_ergodic_eq
  [MeasurableSpace α]
  {μ : Measure α} [IsProbabilityMeasure μ]
  {T : α → α}
  {g : α → ℝ}
-- given
  (hT : Ergodic T μ)
  (hg : Integrable g μ) :
-- imply
  ∀ᵐ x ∂μ, Filter.Tendsto (fun n => birkhoffAverage ℝ T g n x) Filter.atTop
    (nhds (∫ y, g y ∂μ)) := by
-- proof
  apply MathlibExt.Dynamics.Ergodic.BirkhoffWanted.birkhoff_pointwise_ergodic hT hg


-- created on 2026-10-20
