module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Def.Topology.Homotopy.BorsukUlam.Part13


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-! ## Tucker's lemma -/

/-- Tucker's lemma on the grid: an antipodal labeling has a complementary edge. -/
theorem bu_tucker {n m : ℕ} (h0 : 0 < m)
    {L : (Fin n → ℤ) → Bool × Fin n}
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z)) :
    ∃ z ∈ bu_tkBox n m, ∃ w ∈ bu_tkBox n m,
      bu_tkLe z w ∧ L w = bu_tkNeg (L z) := by
  have hm : 1 ≤ m := h0
  by_contra hcon
  have hN : bu_tkNoCompl m L := by
    intro z hz w hw hle heq
    exact hcon ⟨z, hz, w, hw, hle, heq⟩
  have hmem0 : ({0} : Finset (Fin n → ℤ)) ∈ (bu_tkBox n m).powerset := by
    rw [Finset.mem_powerset]
    intro z hz
    rw [Finset.mem_singleton] at hz
    rw [hz]
    exact bu_zero_mem_tkBox
  set v0 : bu_tkV n m := ⟨{0}, hmem0⟩ with hv0def
  have hfilter : Finset.univ.filter
      (fun v => Odd ((bu_tkG n m L hm).degree v)) = {v0} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [bu_degree_odd_iff (hm := hm) hanti hN]
    constructor
    · intro hval
      exact Subtype.ext hval
    · intro he
      rw [he]
  have heven := SimpleGraph.even_card_odd_degree_vertices (bu_tkG n m L hm)
  rw [hfilter, Finset.card_singleton] at heven
  exact (by decide : ¬ Even (1 : ℕ)) heven

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
