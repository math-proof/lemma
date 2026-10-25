/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVPressureConvex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SecantClose.Part3
import Def.StatisticalMechanics.Code.FK.IVPressureConvex.Part3
open MeasureTheory Set Filter Topology Real Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {ι : Type*} [Fintype ι]


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem ivp2_tiltFreeEnergy_eq_Kcgf (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card)
    (t : ℝ) :
    ivp2_tiltFreeEnergy G q t
      = (1 / (G.edgeFinset.card : ℝ))
          * ivp2_Kcgf (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t := by
  unfold ivp2_tiltFreeEnergy ivp2_Kcgf
  set w : ConfigSpace (Sym2 V) → ℝ := fun ω => q ^ numClusters G ω with hw
  set a : ConfigSpace (Sym2 V) → ℝ := fun ω => (openCount G ω : ℝ) with ha
  have hwnn : ∀ ω, 0 ≤ w ω := fun ω => pow_nonneg hq.le _
  have hwpos : ∃ ω, 0 < w ω := ⟨Classical.arbitrary _, pow_pos hq _⟩
  have hSpos : 0 < ivp2_Ssum w a t := ivp2_Ssum_pos w a hwnn hwpos t
  have hEpos : (0:ℝ) < 1 + Real.exp t := by positivity
  have hElt : (0:ℝ) < (1 + Real.exp t) ^ G.edgeFinset.card := by positivity
  have hZ : fkZ G (fsc_logistic t) q = ivp2_Ssum w a t / (1 + Real.exp t) ^ G.edgeFinset.card :=
    ivp2_fkZ_logistic G t q
  rw [hZ, Real.log_div hSpos.ne' hElt.ne', Real.log_pow]
  have hEne : (G.edgeFinset.card : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
  field_simp
  ring


theorem ivp2_tiltFreeEnergy_convexOn (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card) :
    ConvexOn ℝ univ (ivp2_tiltFreeEnergy G q) := by
  set w : ConfigSpace (Sym2 V) → ℝ := fun ω => q ^ numClusters G ω with hw
  set a : ConfigSpace (Sym2 V) → ℝ := fun ω => (openCount G ω : ℝ) with ha
  have hwnn : ∀ ω, 0 ≤ w ω := fun ω => pow_nonneg hq.le _
  have hwpos : ∃ ω, 0 < w ω := ⟨Classical.arbitrary _, pow_pos hq _⟩
  have hconv : ConvexOn ℝ univ (ivp2_Kcgf w a) := ivp2_Kcgf_convexOn w a hwnn hwpos
  have hsmul : ConvexOn ℝ univ (fun t => (1 / (G.edgeFinset.card : ℝ)) * ivp2_Kcgf w a t) := by
    have hc : (0:ℝ) ≤ 1 / (G.edgeFinset.card : ℝ) := by positivity
    exact hconv.smul hc
  have heq : ivp2_tiltFreeEnergy G q
      = fun t => (1 / (G.edgeFinset.card : ℝ)) * ivp2_Kcgf w a t := by
    funext t; exact ivp2_tiltFreeEnergy_eq_Kcgf G q hq hE t
  rw [heq]; exact hsmul


theorem ivp2_convexOn_of_tendsto {κ : Type*} {l : Filter κ} [l.NeBot]
    (f : κ → ℝ → ℝ) (g : ℝ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ univ (f i))
    (hlim : ∀ x, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    ConvexOn ℝ univ g := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t hs ht hst
  have hle : ∀ i, f i (s • x + t • y) ≤ s • f i x + t • f i y := fun i =>
    (hconv i).2 (mem_univ x) (mem_univ y) hs ht hst
  have h1 := hlim (s • x + t • y)
  have h2 : Tendsto (fun i => s • f i x + t • f i y) l (𝓝 (s • g x + t • g y)) :=
    Tendsto.add ((hlim x).const_smul s) ((hlim y).const_smul t)
  exact le_of_tendsto_of_tendsto h1 h2 (Filter.Eventually.of_forall hle)


theorem ivp2_limitFreeEnergy_convexOn
    {κ : Type*} {l : Filter κ} [l.NeBot]
    {W : Type*} [Fintype W] [DecidableEq W]
    (Gn : κ → SimpleGraph W) [∀ i, DecidableRel (Gn i).Adj]
    (q : ℝ) (hq : 0 < q) (hE : ∀ i, 0 < (Gn i).edgeFinset.card)
    (g : ℝ → ℝ)
    (hlim : ∀ t, Tendsto (fun i => ivp2_tiltFreeEnergy (Gn i) q t) l (𝓝 (g t))) :
    ConvexOn ℝ univ g :=
  ivp2_convexOn_of_tendsto (fun i => ivp2_tiltFreeEnergy (Gn i) q) g
    (fun i => ivp2_tiltFreeEnergy_convexOn (Gn i) q hq (hE i)) hlim


theorem ivp2_tiltFreeEnergy_hasDerivAt (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card)
    (t : ℝ) :
    HasDerivAt (ivp2_tiltFreeEnergy G q)
      ((1 / (G.edgeFinset.card : ℝ))
        * (ivp2_S1 (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t
            / ivp2_Ssum (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t)) t := by
  set w : ConfigSpace (Sym2 V) → ℝ := fun ω => q ^ numClusters G ω with hw
  set a : ConfigSpace (Sym2 V) → ℝ := fun ω => (openCount G ω : ℝ) with ha
  have hwnn : ∀ ω, 0 ≤ w ω := fun ω => pow_nonneg hq.le _
  have hwpos : ∃ ω, 0 < w ω := ⟨Classical.arbitrary _, pow_pos hq _⟩
  have heq : ivp2_tiltFreeEnergy G q
      = fun t => (1 / (G.edgeFinset.card : ℝ)) * ivp2_Kcgf w a t := by
    funext t; exact ivp2_tiltFreeEnergy_eq_Kcgf G q hq hE t
  rw [heq]
  exact (ivp2_Kcgf_hasDerivAt w a hwnn hwpos t).const_mul _


theorem ivp2_cgfMean_eq_openCount_expect (q : ℝ) (hq : 0 < q) (t : ℝ) :
    fkExpect G (fsc_logistic t) q (fun ω => (openCount G ω : ℝ))
      = ivp2_S1 (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t
          / ivp2_Ssum (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t := by
  have hSpos : (0:ℝ) < ivp2_Ssum (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t :=
    ivp2_Ssum_pos _ _ (fun ω => pow_nonneg hq.le _) ⟨Classical.arbitrary _, pow_pos hq _⟩ t
  unfold ivp2_Ssum at hSpos
  have hEpos : (0:ℝ) < (1 + Real.exp t) ^ G.edgeFinset.card := by positivity
  unfold fkExpect ivp2_S1 ivp2_Ssum fkProb
  rw [ivp2_fkZ_logistic G t q, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  rw [ivp2_fkWeight_logistic G t q ω]
  unfold ivp2_Ssum
  rw [show (q ^ numClusters G ω * Real.exp ((openCount G ω : ℝ) * t)
        / (1 + Real.exp t) ^ G.edgeFinset.card)
        / ((∑ i, q ^ numClusters G i * Real.exp ((openCount G i : ℝ) * t))
            / (1 + Real.exp t) ^ G.edgeFinset.card)
      = q ^ numClusters G ω * Real.exp ((openCount G ω : ℝ) * t)
          / (∑ i, q ^ numClusters G i * Real.exp ((openCount G i : ℝ) * t)) from
    div_div_div_cancel_right₀ hEpos.ne' _ _]
  rw [div_mul_eq_mul_div]
  ring_nf


theorem ivp2_freeEnergyData_convex_part
    {κ : Type*} {l : Filter κ} [l.NeBot]
    {W : Type*} [Fintype W] [DecidableEq W]
    (Gn : κ → SimpleGraph W) [∀ i, DecidableRel (Gn i).Adj]
    (q : ℝ) (hq : 0 < q) (hE : ∀ i, 0 < (Gn i).edgeFinset.card)
    (g : ℝ → ℝ)
    (hlim : ∀ t, Tendsto (fun i => ivp2_tiltFreeEnergy (Gn i) q t) l (𝓝 (g t))) :
    ConvexOn ℝ univ g :=
  ivp2_limitFreeEnergy_convexOn Gn q hq hE g hlim


end FK
end StatMech
