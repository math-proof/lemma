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
import Def.Topology.Homotopy.BorsukUlam.Part7


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

theorem bu_tkBdry_neg {n m : ℕ} {σ : Finset (Fin n → ℤ)}
    (h : bu_tkBdry m σ) : bu_tkBdry m (σ.image Neg.neg) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨i, hi⟩ := h y hy
  exact ⟨i, by rw [Pi.neg_apply, abs_neg]; exact hi⟩

theorem bu_tkAdj_symm {n : ℕ} {m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ τ : Finset (Fin n → ℤ)} (h : bu_tkAdj m L σ τ) : bu_tkAdj m L τ σ := by
  obtain ⟨hs, ht, hdoor⟩ := h
  refine ⟨ht, hs, ?_⟩
  rcases hdoor with h | h | ⟨hb, rfl⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · refine Or.inr (Or.inr ⟨bu_tkBdry_neg hb, ?_⟩)
    ext y
    constructor
    · intro hy
      refine Finset.mem_image.mpr ⟨-y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, neg_neg y⟩
    · intro hy
      obtain ⟨z, hz, hzz⟩ := Finset.mem_image.mp hy
      obtain ⟨w, hw, hww⟩ := Finset.mem_image.mp hz
      rw [← hww, neg_neg] at hzz
      rw [← hzz]
      exact hw

theorem bu_tkNeg_image_ne {n m : ℕ} (hm : 1 ≤ m)
    {σ : Finset (Fin n → ℤ)} (hchain : bu_tkChain σ) (hb : bu_tkBdry m σ) :
    σ.image Neg.neg ≠ σ := by
  intro heq
  obtain ⟨b, hbσ, _t, _ht, hbot, _htop, _hSeq⟩ := bu_chain_bot_top hchain
  have hnb : -b ∈ σ := by
    rw [← heq]
    exact Finset.mem_image.mpr ⟨b, hbσ, rfl⟩
  have hH : bu_tkH (-b) = bu_tkH b := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.neg_apply]
    exact Int.natAbs_neg _
  have hbb : b = -b := by
    rcases hchain.2 b hbσ (-b) hnb with h | h
    · exact bu_tkLe_of_height_eq h (by omega)
    · exact (bu_tkLe_of_height_eq h (by omega)).symm
  have hb0 : ∀ i, b i = 0 := by
    intro i
    have hi := congrArg (fun z => z i) hbb
    simp only [Pi.neg_apply] at hi
    omega
  obtain ⟨i, hi⟩ := hb b hbσ
  rw [hb0 i, abs_zero] at hi
  have hm0 : m = 0 := by
    have hcast : ((m : ℕ) : ℤ) = 0 := hi.symm
    exact_mod_cast hcast
  omega

theorem bu_tkAdj_irrefl {n : ℕ} {m : ℕ} (hm : 1 ≤ m)
    {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} (h : bu_tkAdj m L σ σ) : False := by
  obtain ⟨hs, _, hdoor⟩ := h
  rcases hdoor with ⟨v, hv, heq, _⟩ | ⟨v, hv, heq, _⟩ | ⟨hb, heq⟩
  · have hcc := congrArg Finset.card heq
    rw [Finset.card_insert_of_notMem hv] at hcc
    omega
  · have hcc := congrArg Finset.card heq
    rw [Finset.card_insert_of_notMem hv] at hcc
    omega
  · exact bu_tkNeg_image_ne hm hs.2.1 hb heq.symm

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
