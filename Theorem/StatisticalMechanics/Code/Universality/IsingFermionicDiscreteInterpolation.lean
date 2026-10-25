/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiscreteInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Mathlib.Topology.UniformSpace.Ascoli
open Filter Metric Set Topology
open scoped UniformConvergence


noncomputable section

namespace StatMech.FrontierA

theorem equicontinuousFamily_restrictionClosure_compact
    {ι : Type*} (F : ι → Complex → Complex)
    (K : Set Complex) (hK : IsCompact K)
    (heq : EquicontinuousOn F K)
    (hbounded : ∃ C : Real, ∀ i z, z ∈ K → ‖F i z‖ ≤ C) :
    IsCompact (closure (Set.range (fun i =>
      UniformFun.ofFun (fun z : K => F i z)))) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : ι → K →ᵤ Complex := fun i => UniformFun.ofFun (fun z => F i z)
  let S : Set (K →ᵤ Complex) := Set.range f
  let sets : Set (Set K) := {Set.univ}
  let eval : (K →ᵤ Complex) → K → Complex := UniformFun.toFun
  have hclosed : IsClosedEmbedding
      (UniformOnFun.ofFun sets ∘ eval) := by
    let e := UniformOnFun.uniformEquivUniformFun Complex sets
      (show Set.univ ∈ sets by simp [sets])
    change IsClosedEmbedding e.symm
    exact e.symm.toHomeomorph.isClosedEmbedding
  have hSEq : EquicontinuousOn (eval ∘ ((↑) : S → K →ᵤ Complex)) Set.univ := by
    rw [equicontinuousOn_univ]
    have hrestrict : Equicontinuous (K.restrict ∘ F) :=
      (equicontinuous_restrict_iff F).2 heq
    let pick : S → ι := fun q => Classical.choose q.property
    have hpick (q : S) : f (pick q) = q := Classical.choose_spec q.property
    have hsub := hrestrict.comp pick
    convert hsub using 1
    funext q z
    have h := congrArg (fun a : K →ᵤ Complex => UniformFun.toFun a z) (hpick q)
    simpa only [f, eval, Function.comp_apply] using h.symm
  obtain ⟨C, hC⟩ := hbounded
  have hpoint : ∀ T ∈ sets, ∀ z ∈ T,
      ∃ Q : Set Complex, IsCompact Q ∧ ∀ q ∈ S, eval q z ∈ Q := by
    intro T hT z _hz
    have hTuniv : T = Set.univ := by
      simpa only [sets, Set.mem_singleton_iff] using hT
    subst T
    refine ⟨closedBall 0 (max C 0), isCompact_closedBall 0 (max C 0), ?_⟩
    intro q hq
    obtain ⟨i, rfl⟩ := hq
    rw [mem_closedBall]
    simpa only [eval, f, dist_zero_right] using
      (hC i z z.property).trans (le_max_left C 0)
  have hcompact : IsCompact (closure S) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖 := sets)
      (fun T hT => by
        have : T = Set.univ := by
          simpa only [sets, Set.mem_singleton_iff] using hT
        subst T
        exact isCompact_univ)
      hclosed
      (fun T hT => by
        have : T = Set.univ := by
          simpa only [sets, Set.mem_singleton_iff] using hT
        subst T
        exact hSEq)
      hpoint
  simpa only [S, f] using hcompact


theorem equicontinuousFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
    (F : Nat → Complex → Complex) (U : Set Complex) (hU : IsOpen U)
    (heq : ∀ K : Set Complex, IsCompact K → K ⊆ U → EquicontinuousOn F K)
    (hbounded : ∀ K : Set Complex, IsCompact K → K ⊆ U →
      ∃ C : Real, ∀ n z, z ∈ K → ‖F n z‖ ≤ C)
    (E : CompactExhaustion U) :
    IsLocallyUniformlySequentiallyPrecompact F U := by
  classical
  intro phi hphi
  let X : Nat → Type := fun n => E.sets n →ᵤ Complex
  let S : ∀ n, Set (X n) := fun n => closure (Set.range (fun k =>
    UniformFun.ofFun (fun z : E.sets n => F (phi k) z)))
  have hS : ∀ n, IsCompact (S n) := by
    intro n
    apply equicontinuousFamily_restrictionClosure_compact
    · exact E.isCompact n
    · exact (heq (E.sets n) (E.isCompact n) (E.subset n)).comp phi
    · obtain ⟨C, hC⟩ := hbounded (E.sets n) (E.isCompact n) (E.subset n)
      exact ⟨C, fun k => hC (phi k)⟩
  let P : Set (∀ n, X n) := Set.univ.pi S
  have hP : IsCompact P := by
    simpa only [P] using isCompact_univ_pi hS
  let x : Nat → ∀ n, X n := fun k n =>
    UniformFun.ofFun (fun z : E.sets n => F (phi k) z)
  have hx : ∀ k, x k ∈ P := by
    intro k n _hn
    exact subset_closure ⟨k, rfl⟩
  obtain ⟨a, ha, psi, hpsi, hlim⟩ := hP.tendsto_subseq hx
  have hcoord : ∀ n, TendstoUniformly
      (fun k (z : E.sets n) => F (phi (psi k)) z)
      (fun z => a n z) atTop := by
    intro n
    have hn : Tendsto (fun k => x (psi k) n) atTop (nhds (a n)) :=
      (tendsto_pi_nhds.mp hlim) n
    have hu := UniformFun.tendsto_iff_tendstoUniformly.mp hn
    simpa only [x, Function.comp_apply] using hu
  let pick : ∀ z : Complex, z ∈ U → Nat := fun z hz =>
    Classical.choose (E.cofinal {z} isCompact_singleton (by simpa using hz))
  have hpick : ∀ (z : Complex) (hz : z ∈ U), z ∈ E.sets (pick z hz) := by
    intro z hz
    exact Classical.choose_spec
      (E.cofinal {z} isCompact_singleton (by simpa using hz)) (by simp)
  let g : Complex → Complex := fun z => if hz : z ∈ U then
    a (pick z hz) ⟨z, hpick z hz⟩ else 0
  have hg_coord : ∀ n z (hz : z ∈ E.sets n), g z = a n ⟨z, hz⟩ := by
    intro n z hz
    have hzU : z ∈ U := E.subset n hz
    simp only [g, dif_pos hzU]
    have hp := (hcoord (pick z hzU)).tendsto_at ⟨z, hpick z hzU⟩
    have hn := (hcoord n).tendsto_at ⟨z, hz⟩
    apply tendsto_nhds_unique
      (show Tendsto (fun k => F (phi (psi k)) z) atTop
        (nhds (a (pick z hzU) ⟨z, hpick z hzU⟩)) by simpa using hp)
    exact (show Tendsto (fun k => F (phi (psi k)) z) atTop
      (nhds (a n ⟨z, hz⟩)) by simpa using hn)
  refine ⟨psi, hpsi, g, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  obtain ⟨n, hKn⟩ := E.cofinal K hK hKU
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hevent := (Metric.tendstoUniformly_iff.mp (hcoord n)) epsilon hepsilon
  filter_upwards [hevent] with k hk
  intro z hz
  rw [hg_coord n z (hKn hz)]
  exact hk ⟨z, hKn hz⟩

end StatMech.FrontierA
end
