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
import Def.Topology.Homotopy.BorsukUlam.Part2


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-! ## Chain cardinality bound -/

/-- The moved sets of a chain form a chain of subsets with the extremal
properties needed for the counting argument. -/
theorem bu_chain_card_bound {n : ℕ} {σ : Finset (Fin n → ℤ)}
    (hσ : bu_tkChain σ) :
    ∃ b ∈ σ, ∃ t ∈ σ, (∀ z ∈ σ, bu_tkLe b z) ∧ (∀ z ∈ σ, bu_tkLe z t) ∧
      bu_tkS σ = bu_tkSgn t ∧
      (σ.image (bu_tkMv b)).card = σ.card ∧
      (∀ A ∈ σ.image (bu_tkMv b), A ⊆ bu_tkMv b t) ∧
      σ.card ≤ (bu_tkMv b t).card + 1 ∧
      (bu_tkMv b t).card ≤ (bu_tkS σ).card ∧
      (σ.card = (bu_tkS σ).card + 1 →
        bu_tkMv b t = Finset.univ.filter (fun i => t i ≠ 0) ∧
        (σ.image (bu_tkMv b)).card = (bu_tkMv b t).card + 1) ∧
      (σ.card = (bu_tkS σ).card →
        (bu_tkMv b t = Finset.univ.filter (fun i => t i ≠ 0) ∧
          (σ.image (bu_tkMv b)).card = (bu_tkMv b t).card) ∨
        (∃ c, Finset.univ.filter (fun i => t i ≠ 0) = insert c (bu_tkMv b t) ∧
          c ∉ bu_tkMv b t ∧
          (σ.image (bu_tkMv b)).card = (bu_tkMv b t).card + 1)) := by
  obtain ⟨b, hbσ, t, htσ, hbot, htop, hSeq⟩ := bu_chain_bot_top hσ
  have hbt : bu_tkLe b t := htop b hbσ
  have hinj : Set.InjOn (bu_tkMv b) (↑σ : Set (Fin n → ℤ)) := by
    intro z hz w hw he
    have hz' : z ∈ σ := Finset.mem_coe.mp hz
    have hw' : w ∈ σ := Finset.mem_coe.mp hw
    have ez : z = bu_tkPt b t (bu_tkMv b z) :=
      (bu_tkMv_normal_a hbt (hbot z hz') (htop z hz')).2
    have ew : w = bu_tkPt b t (bu_tkMv b w) :=
      (bu_tkMv_normal_a hbt (hbot w hw') (htop w hw')).2
    rw [ez, he]
    exact ew.symm
  have hC : (σ.image (bu_tkMv b)).card = σ.card :=
    Finset.card_image_of_injOn hinj
  have hmemC : ∀ A ∈ σ.image (bu_tkMv b), ∀ B ∈ σ.image (bu_tkMv b),
      A ⊆ B ∨ B ⊆ A := by
    intro A hA B hB
    rw [Finset.mem_image] at hA hB
    obtain ⟨z, hz, rfl⟩ := hA
    obtain ⟨w, hw, rfl⟩ := hB
    rcases hσ.2 z hz w hw with h | h
    · exact Or.inl ((bu_tkMv_le_iff hbt (hbot z hz) (htop z hz)
        (hbot w hw) (htop w hw)).mp h)
    · exact Or.inr ((bu_tkMv_le_iff hbt (hbot w hw) (htop w hw)
        (hbot z hz) (htop z hz)).mp h)
  have hsubX : ∀ A ∈ σ.image (bu_tkMv b), A ⊆ bu_tkMv b t := by
    intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨z, hz, rfl⟩ := hA
    exact bu_tkMv_mono_of_le (hbot z hz) hbt (htop z hz)
  have hcard_inj : Set.InjOn Finset.card
      (↑(σ.image (bu_tkMv b)) : Set (Finset (Fin n))) := by
    intro A hA B hB he
    have hA' : A ∈ σ.image (bu_tkMv b) := Finset.mem_coe.mp hA
    have hB' : B ∈ σ.image (bu_tkMv b) := Finset.mem_coe.mp hB
    rcases hmemC A hA' B hB' with h | h
    · exact Finset.eq_of_subset_of_card_le h (le_of_eq he.symm)
    · exact (Finset.eq_of_subset_of_card_le h (le_of_eq he)).symm
  have hcle : (σ.image (bu_tkMv b)).card ≤ (bu_tkMv b t).card + 1 := by
    have himg : (σ.image (bu_tkMv b)).image Finset.card ⊆
        Finset.range ((bu_tkMv b t).card + 1) := by
      intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨A, hA, rfl⟩ := hk
      rw [Finset.mem_range]
      have hAle : A.card ≤ (bu_tkMv b t).card :=
        Finset.card_le_card (hsubX A hA)
      omega
    calc (σ.image (bu_tkMv b)).card = ((σ.image (bu_tkMv b)).image Finset.card).card :=
          (Finset.card_image_of_injOn hcard_inj).symm
      _ ≤ (Finset.range ((bu_tkMv b t).card + 1)).card :=
          Finset.card_le_card himg
      _ = (bu_tkMv b t).card + 1 := Finset.card_range _
  have hXT : bu_tkMv b t ⊆ Finset.univ.filter (fun i => t i ≠ 0) := by
    intro i hi
    rw [bu_tkMv, Finset.mem_filter] at hi
    obtain ⟨_, hne⟩ := hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, bu_tkMv_sub_support hbt i hne⟩
  have hST : (bu_tkS σ).card = (Finset.univ.filter fun i => t i ≠ 0).card := by
    rw [hSeq, bu_tkSgn_card]
  have h1 : σ.card ≤ (bu_tkMv b t).card + 1 := by omega
  have h2 : (bu_tkMv b t).card ≤ (bu_tkS σ).card := by
    calc (bu_tkMv b t).card ≤ (Finset.univ.filter fun i => t i ≠ 0).card :=
          Finset.card_le_card hXT
      _ = (bu_tkS σ).card := hST.symm
  refine ⟨b, hbσ, t, htσ, hbot, htop, hSeq, hC, hsubX, h1, h2, ?_, ?_⟩
  · intro hc
    have hXeq : (bu_tkMv b t).card = (bu_tkS σ).card := by omega
    have hXeqT : bu_tkMv b t = Finset.univ.filter (fun i => t i ≠ 0) :=
      Finset.eq_of_subset_of_card_le hXT (by omega)
    refine ⟨hXeqT, by omega⟩
  · intro hc
    by_cases hXTcard : (bu_tkMv b t).card = (bu_tkS σ).card
    · left
      refine ⟨Finset.eq_of_subset_of_card_le hXT (by omega), by omega⟩
    · right
      have hlt : (bu_tkMv b t).card + 1 = (bu_tkS σ).card := by omega
      have hsd : (Finset.univ.filter (fun i => t i ≠ 0) \ bu_tkMv b t).Nonempty := by
        rw [← Finset.card_pos, Finset.card_sdiff_of_subset hXT]
        omega
      obtain ⟨c, hc⟩ := hsd
      obtain ⟨hcT, hcX⟩ := Finset.mem_sdiff.mp hc
      refine ⟨c, ?_, hcX, by omega⟩
      have hsub : insert c (bu_tkMv b t) ⊆
          Finset.univ.filter (fun i => t i ≠ 0) :=
        Finset.insert_subset hcT hXT
      have hcard : (Finset.univ.filter fun i => t i ≠ 0).card ≤
          (insert c (bu_tkMv b t)).card := by
        rw [Finset.card_insert_of_notMem hcX]
        omega
      exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
