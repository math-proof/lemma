/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.UniformSpace.HeineCantor
import Def.Topology.Homotopy.BorsukUlam


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

theorem bu_tkLe_refl {n : ℕ} (z : Fin n → ℤ) : bu_tkLe z z := fun _ =>
  Or.inl rfl

theorem bu_tkLe_natAbs {n : ℕ} {z w : Fin n → ℤ} (h : bu_tkLe z w)
    (i : Fin n) : (z i).natAbs ≤ (w i).natAbs := by
  rcases h i with hcon | ⟨h0, hw⟩ | ⟨h0, hw⟩ <;> omega

theorem bu_tkLe_height {n : ℕ} {z w : Fin n → ℤ} (h : bu_tkLe z w) :
    bu_tkH z ≤ bu_tkH w :=
  Finset.sum_le_sum fun i _ => bu_tkLe_natAbs h i

theorem bu_tkLe_height_lt {n : ℕ} {z w : Fin n → ℤ} (h : bu_tkLe z w)
    (hne : z ≠ w) : bu_tkH z < bu_tkH w := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  refine Finset.sum_lt_sum (fun j _ => bu_tkLe_natAbs h j) ⟨i, Finset.mem_univ i, ?_⟩
  rcases h i with hcon | ⟨h0, hw⟩ | ⟨h0, hw⟩
  · exact (hi hcon.symm).elim
  · simp only [hw]; omega
  · simp only [hw]; omega

theorem bu_tkLe_of_height_eq {n : ℕ} {z w : Fin n → ℤ} (h : bu_tkLe z w)
    (he : bu_tkH z = bu_tkH w) : z = w := by
  by_contra hne
  exact absurd he (ne_of_lt (bu_tkLe_height_lt h hne))

theorem bu_tkLe_antisymm {n : ℕ} {z w : Fin n → ℤ} (h1 : bu_tkLe z w)
    (h2 : bu_tkLe w z) : z = w := by
  by_contra hne
  have hlt := bu_tkLe_height_lt h1 hne
  have hle := bu_tkLe_height h2
  omega

theorem bu_tkSgn_mono {n : ℕ} {z w : Fin n → ℤ} (h : bu_tkLe z w) :
    bu_tkSgn z ⊆ bu_tkSgn w := by
  intro l hl
  have hl' : z l.2 ≠ 0 ∧ l.1 = decide (0 < z l.2) := bu_mem_tkSgn.mp hl
  obtain ⟨hz0, hbl⟩ := hl'
  have hw0 : w l.2 ≠ 0 := by
    have hle := bu_tkLe_natAbs h l.2
    omega
  have hsign : (0 < w l.2) ↔ (0 < z l.2) := by
    rcases h l.2 with heq | ⟨h0, hw⟩ | ⟨h0, hw⟩
    · rw [heq]
    · constructor <;> intro <;> omega
    · constructor <;> intro <;> omega
  have hdec : decide (0 < w l.2) = decide (0 < z l.2) := by
    simp only [hsign]
  have hbl' : l.1 = decide (0 < w l.2) := by rw [hdec]; exact hbl
  exact bu_mem_tkSgn.mpr ⟨hw0, hbl'⟩

/-- Quasi-transitivity: two steps collapse when the endpoints are comparable. -/
theorem bu_tkLe_trans_of_comparable {n : ℕ} {z w u : Fin n → ℤ}
    (h1 : bu_tkLe z w) (h2 : bu_tkLe w u) (hc : bu_tkLe z u ∨ bu_tkLe u z) :
    bu_tkLe z u := by
  rcases hc with h | h
  · exact h
  · have e1 := bu_tkLe_height h1
    have e2 := bu_tkLe_height h2
    have e3 := bu_tkLe_height h
    have hzw : z = w := bu_tkLe_of_height_eq h1 (by omega)
    subst hzw
    exact h2

/-! ## Chains have a bottom and a top -/

theorem bu_chain_bot_top {n : ℕ} {σ : Finset (Fin n → ℤ)}
    (hσ : bu_tkChain σ) :
    ∃ b ∈ σ, ∃ t ∈ σ, (∀ z ∈ σ, bu_tkLe b z) ∧ (∀ z ∈ σ, bu_tkLe z t) ∧
      bu_tkS σ = bu_tkSgn t := by
  obtain ⟨hne, hcomp⟩ := hσ
  obtain ⟨b, hbσ, hbmin⟩ := Finset.exists_min_image σ bu_tkH hne
  obtain ⟨t, htσ, htmax⟩ := Finset.exists_max_image σ bu_tkH hne
  have hbot : ∀ z ∈ σ, bu_tkLe b z := by
    intro z hz
    rcases hcomp b hbσ z hz with h | h
    · exact h
    · have he : bu_tkH z = bu_tkH b :=
        le_antisymm (bu_tkLe_height h) (hbmin z hz)
      have e : z = b := bu_tkLe_of_height_eq h he
      rw [e]
      exact bu_tkLe_refl b
  have htop : ∀ z ∈ σ, bu_tkLe z t := by
    intro z hz
    rcases hcomp z hz t htσ with h | h
    · exact h
    · have he : bu_tkH t = bu_tkH z :=
        le_antisymm (bu_tkLe_height h) (htmax z hz)
      have e : t = z := bu_tkLe_of_height_eq h he
      rw [e]
      exact bu_tkLe_refl z
  refine ⟨b, hbσ, t, htσ, hbot, htop, ?_⟩
  apply le_antisymm
  · simp only [bu_tkS, Finset.sup_le_iff]
    intro z hz
    exact bu_tkSgn_mono (htop z hz)
  · exact Finset.le_sup htσ

/-- Within a chain, the order is the height order. -/
theorem bu_chain_height_iff {n : ℕ} {σ : Finset (Fin n → ℤ)}
    (hσ : bu_tkChain σ) {z w : Fin n → ℤ} (hz : z ∈ σ) (hw : w ∈ σ) :
    bu_tkLe z w ↔ bu_tkH z ≤ bu_tkH w := by
  constructor
  · exact bu_tkLe_height
  · intro hle
    rcases hσ.2 z hz w hw with h | h
    · exact h
    · have he : bu_tkH z = bu_tkH w := le_antisymm hle (bu_tkLe_height h)
      have e : z = w := (bu_tkLe_of_height_eq h he.symm).symm
      rw [e]
      exact bu_tkLe_refl w

/-- The height is injective on a chain. -/
theorem bu_chain_height_inj {n : ℕ} {σ : Finset (Fin n → ℤ)}
    (hσ : bu_tkChain σ) {z w : Fin n → ℤ} (hz : z ∈ σ) (hw : w ∈ σ)
    (he : bu_tkH z = bu_tkH w) : z = w := by
  rcases hσ.2 z hz w hw with h | h
  · exact bu_tkLe_of_height_eq h he
  · exact (bu_tkLe_of_height_eq h he.symm).symm

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
