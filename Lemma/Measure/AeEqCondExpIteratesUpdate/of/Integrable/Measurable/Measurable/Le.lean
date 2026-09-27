import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import sympy.stats.iterates
import sympy.stats.markov_chain_trajectory
import Lemma.Kernel.MapPartialTraj.eq.ComapLastPowKernelSub.of.Le
open MeasureTheory ProbabilityTheory Finset Kernel Preorder Filtration


@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace Z]
  {n m : ℕ}
  {φ : Z × S → EuclideanVec d}
  {φ₁ : (Iic n → S) → Z}
  {M : HomMarkovChainSpec S}
  {x₀ : Iic 0 → S}
-- given
  (h₀ : n ≤ m)
  (h₁ : Measurable φ)
  (h₂ : Measurable φ₁)
  (h₃ : Integrable (iterates_update h₀ φ φ₁) (M.traj_prob₀ x₀ : Measure (ℕ → S))) :
-- imply
  (M.traj_prob₀ x₀ : Measure (ℕ → S))[iterates_update h₀ φ φ₁ | piLE n] =ᵐ[(M.traj_prob₀ x₀ : Measure (ℕ → S))]
    fun x => ∫ s, φ (φ₁ (frestrictLe n x), s) ∂(M.kernel ^ (m - n)) (x n) := by
-- proof
  have := M.markov_kernel
  change Integrable _ (traj (X := fun _ => S) M.expand_kernel 0 x₀) at h₃
  change (traj (X := fun _ => S) M.expand_kernel 0 x₀)[iterates_update h₀ φ φ₁ | piLE n] =ᵐ[traj (X := fun _ => S) M.expand_kernel 0 x₀] _
  filter_upwards [condExp_traj (X := fun _ => S) (κ := M.expand_kernel) (a := 0) (b := n) (Nat.zero_le n) h₃] with x hx
  refine hx.trans ?_
  let G : (Iic m → S) → EuclideanVec d := fun h => φ (φ₁ (frestrictLe₂ (π := fun _ => S) h₀ h), h ⟨m, mem_Iic.2 le_rfl⟩)
  have hG : Measurable G := h₁.comp ((h₂.comp (measurable_frestrictLe₂ (X := fun _ => S) h₀)).prodMk (measurable_pi_apply _))
  show ∫ y, G (frestrictLe m y) ∂traj (X := fun _ => S) M.expand_kernel n (frestrictLe n x) = _
  rw [← integral_map (measurable_frestrictLe m).aemeasurable hG.aestronglyMeasurable, ← Kernel.map_apply _ (measurable_frestrictLe m), traj_map_frestrictLe]
  have hae : ∀ᵐ h ∂(partialTraj (X := fun _ => S) M.expand_kernel n m (frestrictLe n x)), frestrictLe₂ (π := fun _ => S) h₀ h = frestrictLe n x := by
    have h' : ∀ᵐ y ∂(partialTraj (X := fun _ => S) M.expand_kernel n n (frestrictLe n x)), y = frestrictLe n x := by
      rw [partialTraj_self, Kernel.id_apply]
      exact ae_eq_dirac id
    rw [← partialTraj_map_frestrictLe₂_apply (frestrictLe n x) h₀] at h'
    exact ae_of_ae_map (measurable_frestrictLe₂ (X := fun _ => S) h₀).aemeasurable h'
  rw [integral_congr_ae (g := fun h => φ (φ₁ (frestrictLe n x), h ⟨m, mem_Iic.2 le_rfl⟩)) (hae.mono fun h hh => by simp only [G, hh])]
  rw [← integral_map (φ := fun h : Iic m → S => h ⟨m, mem_Iic.2 le_rfl⟩) (f := fun s => φ (φ₁ (frestrictLe n x), s)) (measurable_pi_apply _).aemeasurable (h₁.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable]
  rw [← Kernel.map_apply _ (measurable_pi_apply _), MapPartialTraj.eq.ComapLastPowKernelSub.of.Le h₀ M]
  rfl


-- created on 2026-09-26