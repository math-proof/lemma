/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BesicovitchKakeya.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.Sets.VietorisTopology
import Mathlib.Topology.Baire.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
open MeasureTheory
open scoped MeasureTheory ENNReal


namespace MathlibExt.MeasureTheory.Geometry.BesicovitchKakeyaWanted

/-- Bowtie: union of slope-`u` segments through the pivot `(c, a)`,
for `u` ranging over `[u₁, u₂]`. -/
def kakBowtie (c a u₁ u₂ : ℝ) : Set (ℝ × ℝ) :=
  (fun p : ℝ × ℝ => (c + p.1 * (p.2 - a), p.2)) '' (Set.Icc u₁ u₂ ×ˢ Set.Icc 0 1)

/-- Slope grid point: `-1 + 2k/N`. -/
noncomputable def kakSlope (N k : ℕ) : ℝ := -1 + 2 * (k : ℝ) / (N : ℝ)

/-- Finite bowtie approximation: a finite set plus `N` consecutive bowties. -/
def kakBowtieApprox (F : Set (ℝ × ℝ)) (N : ℕ) (x : ℕ → ℝ) (a : ℝ) :
    Set (ℝ × ℝ) :=
  F ∪ ⋃ k ∈ (Finset.range N : Set ℕ),
    kakBowtie (x k + kakSlope N k * a) a (kakSlope N k) (kakSlope N (k + 1))

/-- The Kakeya family: nonempty compact sets inside the strip `ℝ × [0,1]`
containing a slope-`u` segment for every `u ∈ [-1,1]`. -/
def kakFamily : Set (TopologicalSpace.NonemptyCompacts (ℝ × ℝ)) :=
  {P | (P : Set (ℝ × ℝ)) ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧
    ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∃ x : ℝ,
      ∀ t ∈ Set.Icc (0 : ℝ) 1, (x + u * t, t) ∈ (P : Set (ℝ × ℝ))}

end MathlibExt.MeasureTheory.Geometry.BesicovitchKakeyaWanted
