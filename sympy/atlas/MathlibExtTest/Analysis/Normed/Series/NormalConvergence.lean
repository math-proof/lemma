/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Normed/Series/NormalConvergence.lean -/


import sympy.atlas.Analysis.Normed.Series.NormalConvergence
import Lemma.Real.NormalConvergence
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Tests for normal convergence of series of functions

Exercises `supNormOn`, `ConvergesNormallyOn`, and
`ConvergesLocallyNormallyOn`: the empty-set and zero-series simp lemmas,
monotonicity under shrinking the domain, projection from local convergence
at a point, and a concrete nonzero one-term series on a singleton domain.
-/


open Topology
open scoped ENNReal

-- `supNormOn` API: empty set, zero function, domain monotonicity.

example (g : ℝ → ℝ) : supNormOn g ∅ = 0 := supNormOn_empty g

example (S : Set ℝ) : supNormOn (0 : ℝ → ℝ) S = 0 := supNormOn_zero S

example {S T : Set ℝ} (h : T ⊆ S) (g : ℝ → ℝ) : supNormOn g T ≤ supNormOn g S :=
  supNormOn_mono h g

-- `ConvergesNormallyOn` API: empty set, zero series, domain monotonicity.

example (f : ℕ → ℝ → ℝ) : ConvergesNormallyOn f ∅ := convergesNormallyOn_empty f

example (S : Set ℝ) : ConvergesNormallyOn (0 : ℕ → ℝ → ℝ) S :=
  convergesNormallyOn_zero S

example {f : ℕ → ℝ → ℝ} {S T : Set ℝ} (h : ConvergesNormallyOn f S)
    (hTS : T ⊆ S) : ConvergesNormallyOn f T :=
  h.mono hTS

-- `ConvergesLocallyNormallyOn` API: empty set, zero series, domain
-- monotonicity, and projection at a point.

example (f : ℕ → ℝ → ℝ) : ConvergesLocallyNormallyOn f ∅ :=
  convergesLocallyNormallyOn_empty f

example (S : Set ℝ) : ConvergesLocallyNormallyOn (0 : ℕ → ℝ → ℝ) S :=
  convergesLocallyNormallyOn_zero S

example {f : ℕ → ℝ → ℝ} {S T : Set ℝ} (h : ConvergesLocallyNormallyOn f S)
    (hTS : T ⊆ S) : ConvergesLocallyNormallyOn f T :=
  h.mono hTS

example {f : ℕ → ℝ → ℝ} {S : Set ℝ} {x : ℝ} (h : ConvergesLocallyNormallyOn f S)
    (hx : x ∈ S) : ∃ U ∈ 𝓝 x, ConvergesNormallyOn f (U ∩ S) :=
  h.exists_nhds_inter hx

/-- A concrete one-term series on `ℝ`: only the `n = 0` term is nonzero. -/
def oneTermSeries : ℕ → ℝ → ℝ := fun n _ => if n = 0 then 1 else 0

/-- The active term is genuinely nonzero on the singleton domain. -/
example : supNormOn (oneTermSeries 0) ({0} : Set ℝ) = 1 := by
  rw [supNormOn_oneTermSeries, ite_eq_left rfl]

/-- The one-term series converges locally normally on the singleton `{0}`. -/
example : ConvergesLocallyNormallyOn oneTermSeries ({0} : Set ℝ) := by
  intro x _
  exact ⟨Set.univ, Filter.univ_mem, by simp [oneTermSeries_normal]⟩
