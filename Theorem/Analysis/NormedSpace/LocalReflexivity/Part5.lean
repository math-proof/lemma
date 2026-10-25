/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Def.Analysis.NormedSpace.LocalReflexivity.Part4


namespace FunctionalAnalysis.LocalReflexivityWanted

variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable section

/-- Claim 1, one coordinate: applying `b j` to the `j`-th coordinate
functional of `ψ = λ ∘ Φ` gives the `β/γ` expansion. -/
theorem plr_claim1_term {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (f : Fin q → StrongDual 𝕜 E) (g : ι → StrongDual 𝕜 E)
    (b : Fin p → StrongDual 𝕜 (StrongDual 𝕜 E))
    (lam : (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) →L[𝕜] 𝕜)
    (psi : (𝕜 × (Fin p → E)) →L[𝕜] 𝕜)
    (hpsi : psi = lam.comp (plr_Phi a c f g)) (j : Fin p) :
    b j ((psi.comp ((ContinuousLinearMap.inr 𝕜 𝕜 (Fin p → E)).comp
      (ContinuousLinearMap.single 𝕜 (fun _ => E) j))) : StrongDual 𝕜 E)
      = (∑ i', lam (0, Pi.single i' (Pi.single j 1), 0) * b j (f i'))
        + ∑ k, ((c k j * lam (0, 0, Pi.single k 1)) * b j (g k)) := by
  have hfun : ((psi.comp ((ContinuousLinearMap.inr 𝕜 𝕜 (Fin p → E)).comp
      (ContinuousLinearMap.single 𝕜 (fun _ => E) j))) : StrongDual 𝕜 E)
      = ((∑ i', lam (0, Pi.single i' (Pi.single j 1), 0) • (f i') :
        StrongDual 𝕜 E)
        + ∑ k, ((c k j * lam (0, 0, Pi.single k 1)) • (g k) :
          StrongDual 𝕜 E)) := by
    ext y
    have eL : ((psi.comp ((ContinuousLinearMap.inr 𝕜 𝕜 (Fin p → E)).comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) j))) : StrongDual 𝕜 E) y
        = lam (0, (fun i' j' => f i' (Pi.single (M := fun _ => E) j y j')),
          (fun k => g k (∑ j', c k j' • Pi.single (M := fun _ => E) j y j'))) := by
      subst hpsi
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
        ContinuousLinearMap.single_apply]
      exact congrArg lam (plr_Phi0 a c f g (Pi.single (M := fun _ => E) j y))
    have eR : ((((∑ i', lam (0, Pi.single i' (Pi.single j 1), 0) • (f i') :
          StrongDual 𝕜 E)
          + ∑ k, ((c k j * lam (0, 0, Pi.single k 1)) • (g k) :
            StrongDual 𝕜 E))) : StrongDual 𝕜 E) y
        = (∑ i', lam (0, Pi.single i' (Pi.single j 1), 0) * f i' y)
          + ∑ k, ((c k j * lam (0, 0, Pi.single k 1)) * g k y) := by
      simp only [sum_apply, add_apply, smul_apply, smul_eq_mul]
    have hmid : ∀ i' : Fin q,
        (∑ j', f i' (Pi.single (M := fun _ => E) j y j')
          * lam (0, Pi.single i' (Pi.single j' 1), 0))
        = lam (0, Pi.single i' (Pi.single j 1), 0) * f i' y := by
      intro i'
      rw [Finset.sum_eq_single j]
      · rw [show Pi.single (M := fun _ => E) j y j = y from
          Pi.single_eq_same (M := fun _ => E) j y]
        exact mul_comm _ _
      · intro j' _ hne
        have hz : Pi.single (M := fun _ => E) j y j' = 0 := by simp [hne]
        rw [hz, map_zero, zero_mul]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have hthird : ∀ k : ι, g k (∑ j', c k j' • Pi.single (M := fun _ => E) j y j')
          * lam (0, 0, Pi.single k 1)
        = ((c k j * lam (0, 0, Pi.single k 1)) * g k y) := by
      intro k
      rw [plr_single_smul_sum, map_smul, smul_eq_mul]
      ring
    have hfst : ∀ (M : Fin q → Fin p → 𝕜) (T : ι → 𝕜),
        (((0, M, T) : 𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜))).1 = 0 :=
      fun M T => rfl
    rw [eL, plr_lam_expand, hfst, zero_mul, zero_add, eR,
      Finset.sum_congr rfl (fun i' _ => hmid i'),
      Finset.sum_congr rfl (fun k _ => hthird k)]
  rw [hfun, map_add, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- Claim 1: the key functional agrees with evaluation at `w` on
functionals of the form `λ ∘ Φ`. -/
theorem plr_claim1 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (f : Fin q → StrongDual 𝕜 E) (g : ι → StrongDual 𝕜 E)
    (b : Fin p → StrongDual 𝕜 (StrongDual 𝕜 E))
    (m : ι → StrongDual 𝕜 (StrongDual 𝕜 E))
    (hm : ∀ k (h : StrongDual 𝕜 E), m k h = h (a k) + ∑ j, c k j * b j h)
    (lam : (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) →L[𝕜] 𝕜) :
    plr_B b (lam.comp (plr_Phi a c f g)) = lam (plr_w b f m g) := by
  have hL10 : (lam.comp (plr_Phi a c f g)) (1, 0)
      = lam (1, 0, 0) + ∑ k, g k (a k) * lam (0, 0, Pi.single k 1) := by
    rw [show (lam.comp (plr_Phi a c f g)) (1, 0)
        = lam (plr_Phi a c f g (1, 0)) from rfl,
      plr_Phi10, plr_lam_expand]
    dsimp only
    simp only [one_mul, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      add_zero]
  have hR : lam (plr_w b f m g)
      = lam (1, 0, 0)
        + ((∑ i', ∑ j, (b j (f i'))
            * lam (0, Pi.single i' (Pi.single j 1), 0))
          + ∑ k, (m k (g k)) * lam (0, 0, Pi.single k 1)) := by
    rw [show plr_w b f m g
        = (1, (fun i j => b j (f i)), (fun k => m k (g k))) from rfl,
      plr_lam_expand]
    dsimp only
    rw [one_mul, add_assoc]
  have hterms : ∀ j : Fin p,
      b j (((lam.comp (plr_Phi a c f g)).comp
        ((ContinuousLinearMap.inr 𝕜 𝕜 (Fin p → E)).comp
          (ContinuousLinearMap.single 𝕜 (fun _ => E) j))) :
        StrongDual 𝕜 E)
      = (∑ i', lam (0, Pi.single i' (Pi.single j 1), 0) * b j (f i'))
        + ∑ k, ((c k j * lam (0, 0, Pi.single k 1)) * b j (g k)) :=
    fun j => plr_claim1_term a c f g b lam _ rfl j
  have hswap1 : (∑ j, ∑ i', lam (0, Pi.single i' (Pi.single j 1), 0)
        * b j (f i'))
      = ∑ i', ∑ j, lam (0, Pi.single i' (Pi.single j 1), 0) * b j (f i') :=
    Finset.sum_comm
  have hswap2 : (∑ j, ∑ k, ((c k j * lam (0, 0, Pi.single k 1)) * b j (g k)))
      = ∑ k, ∑ j, ((c k j * lam (0, 0, Pi.single k 1)) * b j (g k)) :=
    Finset.sum_comm
  have hB : (∑ i', ∑ j, lam (0, Pi.single i' (Pi.single j 1), 0) * b j (f i'))
      = ∑ i', ∑ j, (b j (f i'))
        * lam (0, Pi.single i' (Pi.single j 1), 0) :=
    Finset.sum_congr rfl
      (fun i' _ => Finset.sum_congr rfl (fun j _ => mul_comm _ _))
  have hk : ∀ k : ι, g k (a k) * lam (0, 0, Pi.single k 1)
        + (∑ j, ((c k j * lam (0, 0, Pi.single k 1)) * b j (g k)))
      = m k (g k) * lam (0, 0, Pi.single k 1) := by
    intro k
    rw [hm k (g k), add_mul, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun j _ =>
      show ((c k j * lam (0, 0, Pi.single k 1)) * b j (g k))
        = ((c k j * b j (g k)) * lam (0, 0, Pi.single k 1)) from by ring)]
  have hAC : (∑ k, g k (a k) * lam (0, 0, Pi.single k 1))
        + (∑ k, ∑ j, ((c k j * lam (0, 0, Pi.single k 1)) * b j (g k)))
      = ∑ k, m k (g k) * lam (0, 0, Pi.single k 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => hk k)
  unfold plr_B
  rw [hL10, hR, Finset.sum_congr rfl (fun j _ => hterms j),
    Finset.sum_add_distrib, hswap1, hswap2, hB, ← hAC]
  abel

/-- Claim 2: the key functional on `Ψ ∘ L` equals the sum of the net
point evaluations. -/
theorem plr_claim2 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (b : Fin p → StrongDual 𝕜 (StrongDual 𝕜 E))
    (m : ι → StrongDual 𝕜 (StrongDual 𝕜 E))
    (hm : ∀ k (h : StrongDual 𝕜 E), m k h = h (a k) + ∑ j, c k j * b j h)
    (Psi : (ι → E) →L[𝕜] 𝕜) :
    plr_B b (Psi.comp (plr_L a c))
      = ∑ k, m k (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E) := by
  have hL10 : plr_L a c (1, 0) = a := by
    funext k
    rw [plr_L_apply]
    simp
  have e10 : (Psi.comp (plr_L a c)) (1, 0)
      = ∑ k, (Psi.comp (ContinuousLinearMap.single 𝕜 (fun _ => E) k)) (a k) := by
    rw [show (Psi.comp (plr_L a c)) (1, 0) = Psi (plr_L a c (1, 0)) from rfl,
      hL10]
    exact plr_clm_pi_sum Psi a
  have hfun : ∀ j : Fin p,
      (((Psi.comp (plr_L a c)).comp
        ((ContinuousLinearMap.inr 𝕜 𝕜 (Fin p → E)).comp
          (ContinuousLinearMap.single 𝕜 (fun _ => E) j))) :
        StrongDual 𝕜 E)
      = ((∑ k, c k j • (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E)) :
        StrongDual 𝕜 E) := by
    intro j
    ext y
    have eL : (((Psi.comp (plr_L a c)).comp
        ((ContinuousLinearMap.inr 𝕜 𝕜 (Fin p → E)).comp
          (ContinuousLinearMap.single 𝕜 (fun _ => E) j))) :
        StrongDual 𝕜 E) y
        = Psi (fun k => c k j • y) := by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
        ContinuousLinearMap.single_apply]
      congr 1
      funext k
      rw [plr_L_apply]
      simp only [zero_smul, zero_add]
      exact plr_single_smul_sum (c k) y j
    have eR : ((((∑ k, c k j • (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E)) :
        StrongDual 𝕜 E))) y
        = ∑ k, (c k j * (Psi.comp
          (ContinuousLinearMap.single 𝕜 (fun _ => E) k)) y) := by
      simp only [sum_apply, smul_apply, smul_eq_mul]
    rw [eL, eR, plr_clm_pi_sum Psi (fun k => c k j • y)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    change (Psi.comp (ContinuousLinearMap.single 𝕜 (fun _ => E) k))
      (c k j • y) = _
    rw [map_smul, smul_eq_mul]
  have hbj : ∀ j : Fin p,
      b j (((Psi.comp (plr_L a c)).comp
        ((ContinuousLinearMap.inr 𝕜 𝕜 (Fin p → E)).comp
          (ContinuousLinearMap.single 𝕜 (fun _ => E) j))) :
        StrongDual 𝕜 E)
      = ∑ k, (c k j) * b j (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E) := by
    intro j
    rw [hfun j, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, smul_eq_mul]
  have hswap : (∑ j, ∑ k, (c k j) * b j (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E))
      = ∑ k, ∑ j, (c k j) * b j (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E) :=
    Finset.sum_comm
  have hk : ∀ k : ι, ((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k)) (a k))
        + (∑ j, (c k j) * b j (((Psi.comp
          (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E))
      = m k (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E) :=
    fun k => (hm k _).symm
  have hfin : (∑ k, (Psi.comp
          (ContinuousLinearMap.single 𝕜 (fun _ => E) k)) (a k))
        + (∑ k, ∑ j, (c k j) * b j (((Psi.comp
          (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E))
      = ∑ k, m k (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => hk k)
  unfold plr_B
  rw [e10, Finset.sum_congr rfl (fun j _ => hbj j), hswap]
  exact hfin

/-- Finite `δ`-net of the unit sphere of a finite-dimensional subspace. -/
theorem plr_net_exists
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Mp : Submodule 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)))
    [FiniteDimensional 𝕜 ↥Mp]
    {δ : ℝ} (hδ0 : 0 < δ) :
    ∃ n : ℕ, ∃ mk : Fin n → ↥Mp,
      (∀ k, ‖mk k‖ = 1) ∧ ∀ u : ↥Mp, ‖u‖ = 1 → ∃ k, ‖u - mk k‖ < δ := by
  obtain ⟨t, hts, hfin, hcover⟩ :=
    (isCompact_sphere (0 : ↥Mp) 1).finite_cover_balls hδ0
  have hf : Fintype ↥t := hfin.fintype
  have hmem1 : ∀ x : ↥Mp, x ∈ Metric.sphere (0 : ↥Mp) 1 → ‖x‖ = 1 := by
    intro x hx
    have h := Metric.mem_sphere.mp hx
    rwa [dist_zero_right] at h
  have hmem2 : ∀ x : ↥Mp, ‖x‖ = 1 → x ∈ Metric.sphere (0 : ↥Mp) 1 := by
    intro x hx
    rw [Metric.mem_sphere, dist_zero_right]
    exact hx
  refine ⟨@Fintype.card ↥t hf,
    fun k => ((@Fintype.equivFin ↥t hf).symm k).val, ?_, ?_⟩
  · intro k
    exact hmem1 _ (hts ((@Fintype.equivFin ↥t hf).symm k).prop)
  · intro u hu
    have hcov := hcover (hmem2 u hu)
    simp only [Set.mem_iUnion] at hcov
    obtain ⟨x, hxt, hxu⟩ := hcov
    refine ⟨(@Fintype.equivFin ↥t hf) ⟨x, hxt⟩, ?_⟩
    have hxk : (((@Fintype.equivFin ↥t hf).symm
        ((@Fintype.equivFin ↥t hf) ⟨x, hxt⟩))).val = x := by simp
    have h := Metric.mem_ball.mp hxu
    rw [dist_eq_norm] at h
    simpa [hxk] using h

/-- Norming functionals: an almost-norming `g` with `‖g‖ ≤ 1` for a unit vector. -/
theorem plr_norming
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (u : StrongDual 𝕜 (StrongDual 𝕜 E)) (hu : ‖u‖ = 1)
    {δ : ℝ} (hδ0 : 0 < δ) :
    ∃ g : StrongDual 𝕜 E, ‖g‖ ≤ 1 ∧ 1 - δ ≤ RCLike.re (u g) := by
  have hlt : 1 - δ < ‖u‖ := by linarith
  obtain ⟨g, hg1, hg2⟩ :=
    ContinuousLinearMap.exists_lt_apply_of_lt_opNorm u hlt
  obtain ⟨w, hw1, hw2⟩ := plr_exists_unit_mul (u g)
  refine ⟨w • g, ?_, ?_⟩
  · rw [norm_smul, hw1, one_mul]
    exact hg1.le
  · have e : u (w • g) = w * u g := by rw [map_smul, smul_eq_mul]
    rw [e, hw2]
    exact hg2.le

/-- Scaling a nonzero vector to the unit sphere, with the inverse relation. -/
theorem plr_scale_to_sphere {V : Type*} [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] (m : V) (hm : m ≠ 0) :
    ‖((↑(‖m‖⁻¹) : 𝕜) • m)‖ = 1
      ∧ m = (↑‖m‖ : 𝕜) • ((↑(‖m‖⁻¹) : 𝕜) • m) := by
  have hpos : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have hne : ‖m‖ ≠ 0 := ne_of_gt hpos
  refine ⟨?_, ?_⟩
  · rw [norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ hne]
  · rw [smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ hne,
      RCLike.ofReal_one, one_smul]

/-- Net argument, upper bound: if `T` is bounded by `1 + δ` on a `δ`-net of the
unit sphere, then `‖T‖ ≤ (1 + δ) / (1 - δ)`. -/
theorem plr_opNorm_of_net
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (T : V →L[𝕜] E) {t : Finset V} {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hcover : ∀ m : V, ‖m‖ = 1 → ∃ k ∈ t, ‖m - k‖ < δ)
    (hup : ∀ k ∈ t, ‖T k‖ ≤ 1 + δ) :
    ‖T‖ ≤ (1 + δ) / (1 - δ) := by
  have hδ1' : 0 < 1 - δ := by linarith
  have hMnn : 0 ≤ 1 + δ + ‖T‖ * δ :=
    add_nonneg (add_nonneg zero_le_one hδ0.le)
      (mul_nonneg (norm_nonneg _) hδ0.le)
  have key : ∀ m : V, ‖T m‖ ≤ (1 + δ + ‖T‖ * δ) * ‖m‖ := by
    intro m
    by_cases hm : m = 0
    · subst hm
      simp only [map_zero, norm_zero, mul_zero, le_refl]
    · obtain ⟨hnorm, hback⟩ := plr_scale_to_sphere (𝕜 := 𝕜) m hm
      set u : V := (↑(‖m‖⁻¹) : 𝕜) • m with hu
      obtain ⟨k, hkt, hclose⟩ := hcover u hnorm
      have hkT : ‖T k‖ ≤ 1 + δ := hup k hkt
      have himg : ‖T (u - k)‖ ≤ ‖T‖ * δ := by
        have h1 : ‖T (u - k)‖ ≤ ‖T‖ * ‖u - k‖ :=
          ContinuousLinearMap.le_opNorm _ _
        have h2 : ‖T‖ * ‖u - k‖ ≤ ‖T‖ * δ :=
          mul_le_mul_of_nonneg_left hclose.le (norm_nonneg _)
        linarith
      have hTu : ‖T u‖ ≤ 1 + δ + ‖T‖ * δ := by
        have hkk : k + (u - k) = u := by abel
        have hdecomp : T u = T k + T (u - k) := by
          conv_lhs => rw [← hkk]
          rw [map_add]
        calc ‖T u‖ = ‖T k + T (u - k)‖ := by rw [hdecomp]
        _ ≤ ‖T k‖ + ‖T (u - k)‖ := norm_add_le _ _
        _ ≤ (1 + δ) + ‖T‖ * δ := by linarith
      have hTm : T m = (↑‖m‖ : 𝕜) • T u := by
        conv_lhs => rw [hback, map_smul]
      rw [hTm, norm_smul, RCLike.norm_ofReal,
        abs_of_nonneg (norm_nonneg m), mul_comm ‖m‖]
      exact mul_le_mul_of_nonneg_right hTu (norm_nonneg m)
  have hTop0 : ‖T‖ ≤ 1 + δ + ‖T‖ * δ :=
    ContinuousLinearMap.opNorm_le_bound _ hMnn key
  have h1 : ‖T‖ * δ ≤ ‖T‖ := by
    calc ‖T‖ * δ ≤ ‖T‖ * 1 :=
          mul_le_mul_of_nonneg_left hδ1.le (norm_nonneg _)
    _ = ‖T‖ := mul_one _
  have hexp : ‖T‖ * (1 - δ) = ‖T‖ - ‖T‖ * δ := by ring
  have hTop : ‖T‖ * (1 - δ) ≤ 1 + δ := by linarith
  rw [le_div_iff₀ hδ1']
  exact hTop

/-- Net argument, lower bound: with `‖T‖ ≤ (1 + δ) / (1 - δ)` and `1 - δ ≤ ‖T k‖`
on the net, every vector satisfies `((1 - 3δ) / (1 - δ)) * ‖m‖ ≤ ‖T m‖`. -/
theorem plr_lower_of_net
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (T : V →L[𝕜] E) {t : Finset V} {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hcover : ∀ m : V, ‖m‖ = 1 → ∃ k ∈ t, ‖m - k‖ < δ)
    (hlow : ∀ k ∈ t, 1 - δ ≤ ‖T k‖)
    (hTop : ‖T‖ ≤ (1 + δ) / (1 - δ)) :
    ∀ m : V, ((1 - 3 * δ) / (1 - δ)) * ‖m‖ ≤ ‖T m‖ := by
  have hδ1' : 0 < 1 - δ := by linarith
  have hTop' : ‖T‖ * (1 - δ) ≤ 1 + δ := (le_div_iff₀ hδ1').mp hTop
  have key : ∀ m : V, ((1 - δ) - ‖T‖ * δ) * ‖m‖ ≤ ‖T m‖ := by
    intro m
    by_cases hm : m = 0
    · subst hm
      simp only [map_zero, norm_zero, mul_zero, le_refl]
    · obtain ⟨hnorm, hback⟩ := plr_scale_to_sphere (𝕜 := 𝕜) m hm
      set u : V := (↑(‖m‖⁻¹) : 𝕜) • m with hu
      obtain ⟨k, hkt, hclose⟩ := hcover u hnorm
      have hkT : 1 - δ ≤ ‖T k‖ := hlow k hkt
      have himg : ‖T (k - u)‖ ≤ ‖T‖ * δ := by
        have h1 : ‖T (k - u)‖ ≤ ‖T‖ * ‖k - u‖ :=
          ContinuousLinearMap.le_opNorm _ _
        have h2 : ‖k - u‖ = ‖u - k‖ := norm_sub_rev _ _
        have h3 : ‖T‖ * ‖k - u‖ ≤ ‖T‖ * δ := by
          rw [h2]
          exact mul_le_mul_of_nonneg_left hclose.le (norm_nonneg _)
        linarith
      have hTu : (1 - δ) - ‖T‖ * δ ≤ ‖T u‖ := by
        have hkk : k = u + (k - u) := by abel
        have hdecomp : T k = T u + T (k - u) := by
          have h := congrArg T hkk
          rwa [map_add] at h
        have hle : ‖T k‖ ≤ ‖T u‖ + ‖T (k - u)‖ := by
          rw [hdecomp]
          exact norm_add_le _ _
        linarith
      have hTm : T m = (↑‖m‖ : 𝕜) • T u := by
        conv_lhs => rw [hback, map_smul]
      rw [hTm, norm_smul, RCLike.norm_ofReal,
        abs_of_nonneg (norm_nonneg m), mul_comm ‖m‖]
      exact mul_le_mul_of_nonneg_right hTu (norm_nonneg m)
  have hexpand : ((1 - δ) - ‖T‖ * δ) * (1 - δ)
      = (1 - δ) * (1 - δ) - (‖T‖ * (1 - δ)) * δ := by ring
  have hle : 1 - 3 * δ ≤ ((1 - δ) - ‖T‖ * δ) * (1 - δ) := by
    have hmul : (‖T‖ * (1 - δ)) * δ ≤ (1 + δ) * δ :=
      mul_le_mul_of_nonneg_right hTop' hδ0.le
    have hring : (1 - δ) * (1 - δ) - (1 + δ) * δ = 1 - 3 * δ := by ring
    linarith
  have hC : (1 - 3 * δ) / (1 - δ) ≤ (1 - δ) - ‖T‖ * δ := by
    rw [div_le_iff₀ hδ1']
    exact hle
  intro m
  have hm := key m
  have hmul := mul_le_mul_of_nonneg_right hC (norm_nonneg m)
  linarith

/-- Helly's lemma, general form: a finite system of linear equations with one norm
bound is solvable whenever the dual inequality holds. -/
theorem plr_helly
    {Z Y V : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (L : Z →L[𝕜] Y) (Φ : Z →L[𝕜] V) (w : V) {s r : ℝ} (hs : 0 ≤ s)
    (hsr : s < r)
    (hD : ∀ lam : V →L[𝕜] 𝕜, ∀ Psi : Y →L[𝕜] 𝕜,
      lam.comp Φ = Psi.comp L → RCLike.re (lam w) ≤ s * ‖Psi‖) :
    ∃ z : Z, ‖L z‖ < r ∧ Φ z = w := by
  have hr0 : 0 < r := lt_of_le_of_lt hs hsr
  -- Step 1: `w` lies in the range of `Φ`.
  have hmem : w ∈ Φ.range := by
    by_contra hw
    obtain ⟨lam0, hne, hbot⟩ :=
      Submodule.exists_dual_map_eq_bot_of_notMem (p := Φ.range) (x := w)
        hw inferInstance
    have hw1 : ((lam0 w)⁻¹ • lam0) w = 1 := by
      rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hne]
    have hvan : ∀ z : Z, lam0 (Φ z) = 0 := by
      intro z
      have hm : lam0 (Φ z) ∈ Submodule.map lam0 Φ.range :=
        ⟨Φ z, ⟨z, rfl⟩, rfl⟩
      rw [hbot] at hm
      exact (Submodule.mem_bot 𝕜).mp hm
    set lam1c : V →L[𝕜] 𝕜 :=
      LinearMap.toContinuousLinearMap ((lam0 w)⁻¹ • lam0) with hlam1c
    have hlc : ∀ v : V, lam1c v = ((lam0 w)⁻¹ • lam0) v := fun v => rfl
    have hw1c : lam1c w = 1 := hw1
    have hcomp : lam1c.comp Φ = 0 := by
      ext z
      simp only [ContinuousLinearMap.comp_apply, zero_apply]
      rw [hlc, LinearMap.smul_apply, hvan z, smul_zero]
    have hD0 := hD lam1c 0 (by simp [hcomp])
    simp only [hw1c, RCLike.one_re, norm_zero, mul_zero] at hD0
    linarith
  -- Step 2 setup: the restricted map, the sublevel set and its image.
  have hsurj : Function.Surjective (Φ.rangeRestrict) := by
    intro y
    obtain ⟨z, hz⟩ := y.prop
    exact ⟨z, Subtype.ext (by simpa using hz)⟩
  have hsurj' : Function.Surjective (Φ.rangeRestrict.toLinearMap) := hsurj
  have hopen : IsOpenMap (Φ.rangeRestrict) :=
    LinearMap.isOpenMap_of_finiteDimensional _ hsurj'
  set C : Set Z := L ⁻¹' Metric.ball (0 : Y) r with hC
  have hCopen : IsOpen C := Metric.isOpen_ball.preimage L.continuous
  have hCconv : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    have hx' : ‖L x‖ < r := by
      have h := Metric.mem_ball.mp hx
      rwa [dist_zero_right] at h
    have hy' : ‖L y‖ < r := by
      have h := Metric.mem_ball.mp hy
      rwa [dist_zero_right] at h
    have e1 : a • x = ((a : 𝕜)) • x := RCLike.real_smul_eq_coe_smul a x
    have e2 : b • y = ((b : 𝕜)) • y := RCLike.real_smul_eq_coe_smul b y
    have hL : L (a • x + b • y) = (a : 𝕜) • L x + (b : 𝕜) • L y := by
      rw [e1, e2, map_add, map_smul, map_smul]
    have hfin : a * ‖L x‖ + b * ‖L y‖ < r := by
      have h1 : a * ‖L x‖ ≤ a * r := mul_le_mul_of_nonneg_left hx'.le ha
      have h2 : b * ‖L y‖ ≤ b * r := mul_le_mul_of_nonneg_left hy'.le hb
      have h3 : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
      rcases eq_or_ne a 0 with rfl | ha0
      · have hb1 : b = 1 := by linarith
        rw [zero_mul, zero_add, hb1, one_mul]
        exact hy'
      · have ha0' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hlt1 : a * ‖L x‖ < a * r := mul_lt_mul_of_pos_left hx' ha0'
        linarith
    have hmemC : L (a • x + b • y) ∈ Metric.ball (0 : Y) r := by
      rw [Metric.mem_ball, dist_zero_right, hL]
      calc ‖(a : 𝕜) • L x + (b : 𝕜) • L y‖
          ≤ ‖(a : 𝕜) • L x‖ + ‖(b : 𝕜) • L y‖ := norm_add_le _ _
        _ = a * ‖L x‖ + b * ‖L y‖ := by
          rw [norm_smul, norm_smul, RCLike.norm_ofReal, RCLike.norm_ofReal,
            abs_of_nonneg ha, abs_of_nonneg hb]
        _ < r := hfin
    exact hmemC
  have hImOpen : IsOpen (Φ.rangeRestrict '' C) := hopen _ hCopen
  have hImConv : Convex ℝ (Φ.rangeRestrict '' C) := by
    intro y1 hy1 y2 hy2 a b ha hb hab
    obtain ⟨x1, hx1C, rfl⟩ := hy1
    obtain ⟨x2, hx2C, rfl⟩ := hy2
    refine ⟨a • x1 + b • x2, hCconv hx1C hx2C ha hb hab, ?_⟩
    have e1 : a • x1 = ((a : 𝕜)) • x1 := RCLike.real_smul_eq_coe_smul a x1
    have e2 : b • x2 = ((b : 𝕜)) • x2 := RCLike.real_smul_eq_coe_smul b x2
    have e3 : a • Φ.rangeRestrict x1 = ((a : 𝕜)) • Φ.rangeRestrict x1 :=
      RCLike.real_smul_eq_coe_smul a _
    have e4 : b • Φ.rangeRestrict x2 = ((b : 𝕜)) • Φ.rangeRestrict x2 :=
      RCLike.real_smul_eq_coe_smul b _
    rw [e3, e4, ← map_smul, ← map_smul, ← map_add, ← e1, ← e2]
  by_contra hcon
  have hcon' : ∀ z : Z, ‖L z‖ < r → Φ z ≠ w := fun z hz he => hcon ⟨z, hz, he⟩
  set w' : ↥(Φ.range) := ⟨w, hmem⟩ with hw'
  have hnotmem : w' ∉ Φ.rangeRestrict '' C := by
    rintro ⟨z, hzC, hzz⟩
    have hzC' : ‖L z‖ < r := by
      have h := Metric.mem_ball.mp hzC
      rwa [dist_zero_right] at h
    have hzw : Φ z = w := by
      have h := Subtype.ext_iff.mp hzz
      simpa using h
    exact hcon' z hzC' hzw
  obtain ⟨mu, hmu⟩ :=
    RCLike.geometric_hahn_banach_open_point (𝕜 := 𝕜) (E := ↥(Φ.range))
      hImConv hImOpen hnotmem
  obtain ⟨lam, hlamEq, -⟩ := exists_extension_norm_eq (Φ.range) mu
  set beta : ℝ := RCLike.re (lam w) with hbeta
  have hbeta0 : 0 < beta := by
    have h0C : (0 : Z) ∈ C := by
      have hmem7 : L (0 : Z) ∈ Metric.ball (0 : Y) r := by
        rw [Metric.mem_ball, map_zero, dist_zero_right, norm_zero]
        exact hr0
      exact hmem7
    have him := hmu (Φ.rangeRestrict 0) ⟨0, h0C, rfl⟩
    have ew : ((w' : ↥(Φ.range)) : V) = w := rfl
    rw [map_zero, map_zero, RCLike.zero_re, ← hlamEq, ew, ← hbeta] at him
    exact him
  have e2 : mu w' = lam w := (hlamEq w').symm
  have hltC : ∀ z : Z, z ∈ C → RCLike.re (lam (Φ z)) < beta := by
    intro z hz
    have him := hmu (Φ.rangeRestrict z) ⟨z, hz, rfl⟩
    have h := hlamEq (Φ.rangeRestrict z)
    have e : ((Φ.rangeRestrict z : ↥(Φ.range)) : V) = Φ z := rfl
    rw [e] at h
    rw [h, hbeta, ← e2]
    exact him
  -- Step 3: every value of `lam ∘ Φ` is controlled by `L`.
  have hbound : ∀ z : Z, ‖lam (Φ z)‖ ≤ (beta / r) * ‖L z‖ := by
    intro z
    by_contra hlt
    have hlt : (beta / r) * ‖L z‖ < ‖lam (Φ z)‖ := lt_of_not_ge hlt
    have hc0 : lam (Φ z) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hlt
      have hnn : 0 ≤ (beta / r) * ‖L z‖ :=
        mul_nonneg (div_nonneg hbeta0.le hr0.le) (norm_nonneg _)
      linarith
    have hcn : 0 < ‖lam (Φ z)‖ := norm_pos_iff.mpr hc0
    have hkey : beta * ‖L z‖ < r * ‖lam (Φ z)‖ := by
      have h := hlt
      rw [div_mul_eq_mul_div, div_lt_iff₀ hr0] at h
      linarith
    set d : 𝕜 := (↑(beta / ‖lam (Φ z)‖ ^ 2) : 𝕜) * starRingEnd 𝕜 (lam (Φ z))
      with hd
    set z' : Z := d • z with hz'
    have hne2 : (‖lam (Φ z)‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hcn.ne'
    have hlamz' : lam (Φ z') = (↑beta : 𝕜) := by
      have e1 : Φ z' = d • Φ z := by rw [hz', map_smul]
      have e2' : lam (d • Φ z) = d • lam (Φ z) := by rw [map_smul]
      rw [e1, e2', hd, smul_eq_mul, mul_assoc, RCLike.conj_mul,
        ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, div_mul_cancel₀ _ hne2]
    have hnormz' : ‖L z'‖ < r := by
      have e1 : L z' = d • L z := by rw [hz', map_smul]
      rw [e1, norm_smul, hd, norm_mul, RCLike.norm_ofReal, RCLike.norm_conj,
        abs_of_nonneg (div_nonneg hbeta0.le (by positivity))]
      have e3 : beta / ‖lam (Φ z)‖ ^ 2 * ‖lam (Φ z)‖ * ‖L z‖
          = beta * ‖L z‖ / ‖lam (Φ z)‖ := by
        field_simp
      rw [e3, div_lt_iff₀ hcn]
      exact hkey
    have hmemC : z' ∈ C := by
      have hmem7 : L z' ∈ Metric.ball (0 : Y) r := by
        rw [Metric.mem_ball, dist_zero_right]
        exact hnormz'
      exact hmem7
    have hlt2 := hltC z' hmemC
    rw [hlamz', RCLike.ofReal_re] at hlt2
    exact lt_irrefl _ hlt2
  -- Step 4: factor `lam ∘ Φ` through `L`.
  have hker : LinearMap.ker L.toLinearMap
      ≤ LinearMap.ker (lam.comp Φ).toLinearMap := by
    intro z hz
    have hz' : L z = 0 := LinearMap.mem_ker.mp hz
    have hb := hbound z
    rw [hz', norm_zero, mul_zero] at hb
    have h0 : lam (Φ z) = 0 :=
      norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
    refine LinearMap.mem_ker.mpr ?_
    have e : (lam.comp Φ).toLinearMap z = lam (Φ z) := rfl
    rw [e]
    exact h0
  set qe := LinearMap.quotKerEquivRange L.toLinearMap with hqe
  set phi1 : ↥(LinearMap.range L.toLinearMap) →ₗ[𝕜] 𝕜 :=
    (Submodule.liftQ (LinearMap.ker L.toLinearMap) (lam.comp Φ).toLinearMap
      hker).comp qe.symm.toLinearMap with hphi1
  have hphi1 : ∀ z : Z, phi1 ⟨L.toLinearMap z, z, rfl⟩ = lam (Φ z) := by
    intro z
    have hsym : qe.symm ⟨L.toLinearMap z, z, rfl⟩
        = Submodule.Quotient.mk z := by
      apply qe.injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      exact (LinearMap.quotKerEquivRange_apply_mk _ z).symm
    have hsym' : qe.symm.toLinearMap ⟨L.toLinearMap z, z, rfl⟩
        = Submodule.Quotient.mk z :=
      hsym
    rw [hphi1, LinearMap.comp_apply, hsym']
    exact Submodule.liftQ_apply _ _ z
  have hphi1bd : ∀ y : ↥(LinearMap.range L.toLinearMap),
      ‖phi1 y‖ ≤ (beta / r) * ‖(y : Y)‖ := by
    rintro ⟨y, z, rfl⟩
    rw [hphi1]
    exact hbound z
  set Psi0 : ↥(LinearMap.range L.toLinearMap) →L[𝕜] 𝕜 :=
    LinearMap.mkContinuous phi1 (beta / r) hphi1bd with hPsi0
  have hPsi0bd : ‖Psi0‖ ≤ beta / r :=
    LinearMap.mkContinuous_norm_le _ (div_nonneg hbeta0.le hr0.le) _
  obtain ⟨Psi, hPsiEq, hPsiNorm⟩ :=
    exists_extension_norm_eq (LinearMap.range L.toLinearMap) Psi0
  have hPsi : ‖Psi‖ ≤ beta / r := hPsiNorm ▸ hPsi0bd
  have hPsiSpec : ∀ z : Z, Psi (L z) = lam (Φ z) := by
    intro z
    have h1 := hPsiEq (⟨L.toLinearMap z, z, rfl⟩
      : ↥(LinearMap.range L.toLinearMap))
    have h2 : Psi0 ⟨L.toLinearMap z, z, rfl⟩
        = phi1 ⟨L.toLinearMap z, z, rfl⟩ := rfl
    have h3 : ((⟨L.toLinearMap z, z, rfl⟩
      : ↥(LinearMap.range L.toLinearMap)) : Y) = L z := rfl
    rw [h3] at h1
    rw [h1, h2, hphi1]
  have hcomp2 : lam.comp Φ = Psi.comp L := by
    ext z
    simp only [ContinuousLinearMap.comp_apply]
    exact (hPsiSpec z).symm
  -- Step 5: the dual inequality contradicts `beta > 0`.
  have hle := hD lam Psi hcomp2
  rw [← hbeta] at hle
  have h3 : s * ‖Psi‖ ≤ s * (beta / r) :=
    mul_le_mul_of_nonneg_left hPsi hs
  have h4 : s * (beta / r) < beta := by
    have h1 : s * beta < beta * r := by
      have h := mul_lt_mul_of_pos_right hsr hbeta0
      linarith
    have h2 : s * (beta / r) = (s * beta) / r := by ring
    rw [h2, div_lt_iff₀ hr0]
    exact h1
  linarith

/-- Evaluation at a point, summed over an orthonormal-style decomposition, is bounded
by the operator norm: the `ℓ¹` bound on a product dual. -/
theorem plr_sum_norm_single_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (Psi : (ι → E) →L[𝕜] 𝕜) :
    ∑ k, ‖Psi.comp (ContinuousLinearMap.single 𝕜 (fun _ => E) k)‖ ≤ ‖Psi‖ := by
  set psi : ι → E →L[𝕜] 𝕜 :=
    fun k => Psi.comp (ContinuousLinearMap.single 𝕜 (fun _ => E) k) with hpsi
  have hsum : ∀ v : ι → E, Psi v = ∑ k, psi k (v k) := by
    intro v
    have h : v = ∑ k, Pi.single k (v k) := (Finset.univ_sum_single v).symm
    conv_lhs => rw [h]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [hpsi, ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
  have key : ∀ eta : ℝ, 0 < eta →
      ∑ k, ‖psi k‖ ≤ ‖Psi‖ + (Fintype.card ι) * eta := by
    intro eta heta
    have hex : ∀ k : ι, ∃ x : E, ‖x‖ ≤ 1 ∧ ‖psi k‖ - eta ≤ ‖psi k x‖ := by
      intro k
      by_cases hk : psi k = 0
      · refine ⟨0, by simp, ?_⟩
        rw [hk, norm_zero, zero_apply, norm_zero, zero_sub]
        exact neg_nonpos.mpr heta.le
      · have hlt : ‖psi k‖ - eta < ‖psi k‖ := by linarith
        obtain ⟨x, hx1, hx2⟩ :=
          ContinuousLinearMap.exists_lt_apply_of_lt_opNorm (psi k) hlt
        exact ⟨x, hx1.le, hx2.le⟩
    choose x hx1 hx2 using hex
    have hrot : ∀ k : ι, ∃ y : E,
        ‖y‖ ≤ 1 ∧ ‖psi k (x k)‖ ≤ RCLike.re (psi k y) := by
      intro k
      obtain ⟨u, hu1, hu2⟩ := plr_exists_unit_mul (psi k (x k))
      refine ⟨u • x k, ?_, ?_⟩
      · rw [norm_smul, hu1, one_mul]
        exact hx1 k
      · have e : psi k (u • x k) = u * psi k (x k) := by
          rw [map_smul, smul_eq_mul]
        rw [e, hu2]
    choose y hy1 hy2 using hrot
    have hvn : ‖y‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro k
      exact hy1 k
    have hre : RCLike.re (Psi y) = ∑ k, RCLike.re (psi k (y k)) := by
      rw [hsum y]
      have h : ∀ s : Finset ι, RCLike.re (s.sum fun k => psi k (y k))
          = s.sum fun k => RCLike.re (psi k (y k)) := by
        intro s
        induction s using Finset.induction with
        | empty => simp only [Finset.sum_empty, RCLike.zero_re]
        | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add RCLike.re, ih]
      exact h Finset.univ
    have hfin : ∑ k, ‖psi k‖ ≤ ‖Psi‖ + (Fintype.card ι) * eta := by
      have h1 : ∑ k, (‖psi k‖ - eta) ≤ RCLike.re (Psi y) := by
        rw [hre]
        apply Finset.sum_le_sum
        intro k _
        have a := hx2 k
        have b := hy2 k
        linarith
      have h2 : RCLike.re (Psi y) ≤ ‖Psi‖ := by
        have a : RCLike.re (Psi y) ≤ ‖Psi y‖ := RCLike.re_le_norm _
        have b : ‖Psi y‖ ≤ ‖Psi‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
        have c : ‖Psi‖ * ‖y‖ ≤ ‖Psi‖ * 1 :=
          mul_le_mul_of_nonneg_left hvn (ContinuousLinearMap.opNorm_nonneg _)
        linarith
      have h3 : ∑ k, (‖psi k‖ - eta)
          = (∑ k, ‖psi k‖) - (Fintype.card ι) * eta := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
      linarith
    exact hfin
  apply le_of_forall_pos_le_add
  intro eps heps
  by_cases hcard : Fintype.card ι = 0
  · have h0 : ∑ k, ‖psi k‖ ≤ ‖Psi‖ := by
      have h := key 1 one_pos
      rw [hcard] at h
      simpa using h
    linarith [ContinuousLinearMap.opNorm_nonneg Psi, heps.le,
      add_nonneg (norm_nonneg (‖Psi‖)) heps.le]
  · have hpos : 0 < (Fintype.card ι : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard)
    have h := key (eps / Fintype.card ι) (div_pos heps hpos)
    have hcancel : (Fintype.card ι : ℝ) * (eps / Fintype.card ι) = eps := by
      field_simp
    linarith

/-- Dual inequality: the Helly hypothesis (D) with `s = 1`. -/
theorem plr_dual_ineq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (f : Fin q → StrongDual 𝕜 E) (g : ι → StrongDual 𝕜 E)
    (b : Fin p → StrongDual 𝕜 (StrongDual 𝕜 E))
    (m : ι → StrongDual 𝕜 (StrongDual 𝕜 E))
    (hm : ∀ k (h : StrongDual 𝕜 E), m k h = h (a k) + ∑ j, c k j * b j h)
    (hmnorm : ∀ k, ‖m k‖ = 1)
    (lam : (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) →L[𝕜] 𝕜)
    (Psi : (ι → E) →L[𝕜] 𝕜)
    (hcomp : lam.comp (plr_Phi a c f g) = Psi.comp (plr_L a c)) :
    RCLike.re (lam (plr_w b f m g)) ≤ 1 * ‖Psi‖ := by
  have hterm : ∀ k : ι,
      ‖m k (((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E)‖
      ≤ ‖(((Psi.comp
        (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E)‖ := by
    intro k
    calc ‖m k (((Psi.comp
            (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E)‖
        ≤ ‖m k‖ * ‖(((Psi.comp
            (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖(((Psi.comp
            (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) :
            StrongDual 𝕜 E)‖ := by
          rw [hmnorm k, one_mul]
  rw [← plr_claim1 a c f g b m hm lam, hcomp,
    plr_claim2 a c b m hm Psi, one_mul, plr_re_sum]
  exact calc ∑ k, RCLike.re (m k (((Psi.comp
              (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) : StrongDual 𝕜 E))
          ≤ ∑ k, ‖m k (((Psi.comp
              (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) :
              StrongDual 𝕜 E)‖ :=
            Finset.sum_le_sum (fun k _ => RCLike.re_le_norm _)
        _ ≤ ∑ k, ‖(((Psi.comp
              (ContinuousLinearMap.single 𝕜 (fun _ => E) k))) :
              StrongDual 𝕜 E)‖ :=
            Finset.sum_le_sum (fun k _ => hterm k)
        _ ≤ ‖Psi‖ := plr_sum_norm_single_le Psi

/-- Solving the finite system via Helly's lemma. The solution `y` satisfies
the dual pairings, the norming equations and the norm bound at every net point. -/
theorem plr_solve {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {p q : ℕ} {ι : Type*} (hF : Fintype ι)
    (a : ι → E) (c : ι → Fin p → 𝕜)
    (f : Fin q → StrongDual 𝕜 E) (g : ι → StrongDual 𝕜 E)
    (b : Fin p → StrongDual 𝕜 (StrongDual 𝕜 E))
    (m : ι → StrongDual 𝕜 (StrongDual 𝕜 E))
    (hm : ∀ k (h : StrongDual 𝕜 E), m k h = h (a k) + ∑ j, c k j * b j h)
    (hmnorm : ∀ k, ‖m k‖ = 1)
    {δ : ℝ} (hδ0 : 0 < δ) :
    ∃ y : Fin p → E,
      (∀ i j, f i (y j) = b j (f i))
      ∧ (∀ k, g k (a k + ∑ j, c k j • y j) = m k (g k))
      ∧ (∀ k, ‖a k + ∑ j, c k j • y j‖ < 1 + δ) := by
  classical
  have hw : plr_w b f m g
      = (1, (fun i j => b j (f i)), (fun k => m k (g k))) := rfl
  have hD : ∀ lam : (𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜)) →L[𝕜] 𝕜,
      ∀ Psi : (ι → E) →L[𝕜] 𝕜,
      lam.comp (plr_Phi a c f g) = Psi.comp (plr_L a c) →
      RCLike.re (lam (plr_w b f m g)) ≤ 1 * ‖Psi‖ :=
    fun lam Psi hcomp => plr_dual_ineq a c f g b m hm hmnorm lam Psi hcomp
  obtain ⟨z, hzL, hzPhi⟩ := plr_helly (plr_L a c) (plr_Phi a c f g)
    (plr_w b f m g) zero_le_one (by linarith : (1 : ℝ) < 1 + δ) hD
  have ePhi : plr_w b f m g
      = (z.1, (fun i j => f i (z.2 j)),
        (fun k => g k (plr_L a c z k))) := by
    rw [← hzPhi]
    exact plr_Phi_apply a c f g z
  have ht : z.1 = 1 := by
    have h := congrArg Prod.fst ePhi
    rw [hw] at h
    simpa using h.symm
  have hLk : ∀ k, plr_L a c z k = a k + ∑ j, c k j • z.2 j := by
    intro k
    rw [plr_L_apply, ht, one_smul]
  have hmid : ∀ i j, f i (z.2 j) = b j (f i) := by
    intro i j
    have h := congrArg (fun v : 𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜) =>
      v.2.1 i j) ePhi
    rw [hw] at h
    simpa using h.symm
  have hlast : ∀ k, g k (a k + ∑ j, c k j • z.2 j) = m k (g k) := by
    intro k
    have h2 : m k (g k) = g k (plr_L a c z k) := by
      have h := congrArg (fun v : 𝕜 × (Fin q → Fin p → 𝕜) × (ι → 𝕜) =>
        v.2.2 k) ePhi
      rw [hw] at h
      simpa using h
    rw [hLk k] at h2
    exact h2.symm
  have hnorm : ∀ k, ‖a k + ∑ j, c k j • z.2 j‖ < 1 + δ := by
    intro k
    rw [← hLk k]
    exact lt_of_le_of_lt (norm_le_pi_norm (plr_L a c z) k) hzL
  exact ⟨z.2, hmid, hlast, hnorm⟩

end
end FunctionalAnalysis.LocalReflexivityWanted
