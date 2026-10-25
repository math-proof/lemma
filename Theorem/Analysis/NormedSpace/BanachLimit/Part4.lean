import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Def.Analysis.NormedSpace.BanachLimit.Part4
/-!
# Banach limits on bounded real sequences

A Banach limit is a positive shift-invariant continuous real-linear functional
on `ℕ →ᵇ ℝ` extending ordinary limits. Following Banach, the ordinary limit
functional on convergent sequences is dominated by the sublinear functional
`M x = limsup (Cesàro means of x)` and extended by Hahn–Banach
(`exists_extension_of_le_sublinear`); the bound `|L| ≤ ‖·‖` gives continuity,
and shift-invariance holds because the Cesàro means of `Sx - x` telescope to
`(x n - x 0) / n → 0`.

Source: S. Banach, *Théorie des opérations linéaires* (1932); G. G. Lorentz,
"A contribution to the theory of divergent sequences", *Acta Mathematica* 80
(1948), 167–190, DOI `10.1007/BF02393648`.
-/


namespace FunctionalAnalysis.BanachLimit

open scoped BoundedContinuousFunction

noncomputable section

lemma extension_spec :
    (∀ x : pmap.domain, extension (x : BoundedSeq) = pmap x) ∧ ∀ x, extension x ≤ limsupCes x :=
  Classical.choose_spec
    (exists_extension_of_le_sublinear pmap limsupCes limsupCes_hom
      limsupCes_add pmap_le)

lemma extension_eq_lim (x : pmap.domain) : extension (x : BoundedSeq) = pmap x :=
  extension_spec.1 x

lemma extension_le (x : BoundedSeq) : extension x ≤ limsupCes x :=
  extension_spec.2 x

/-- The extension is bounded by the norm. -/
lemma extension_bound (x : BoundedSeq) : |extension x| ≤ ‖x‖ := by
  have h1 : extension x ≤ limsupCes x := extension_le x
  have h2 : extension (-x) ≤ limsupCes (-x) := extension_le (-x)
  have hNx : limsupCes x ≤ ‖x‖ := limsupCes_bound x
  have hNnx : limsupCes (-x) ≤ ‖x‖ := by
    simpa using limsupCes_bound (-x)
  have hne : extension (-x) = -extension x := map_neg _ _
  rw [abs_le]
  constructor <;> linarith

/-- Telescoping: means of `Sx - x` equal `(x n - x 0) / n`. -/
lemma cesMean_shift_sub (x : BoundedSeq) (n : ℕ) :
    cesMean (shift x - x) n = (x n - x 0) / (n : ℝ) := by
  have h : (fun i => (shift x) i - x i) = (fun i => x (i + 1) - x i) :=
    funext fun i => by rw [shift_apply]
  have esum : ∑ i ∈ Finset.range n, ((shift x) i - x i) = x n - x 0 := by
    rw [h]
    have t := Finset.sum_range_sub' (fun i => x i) n
    have neg : (∑ i ∈ Finset.range n, (x (i + 1) - x i))
        = -(∑ i ∈ Finset.range n, (x i - x (i + 1))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [neg, t, neg_sub]
  unfold cesMean
  simp only [BoundedContinuousFunction.sub_apply, esum]
  rw [div_eq_mul_inv, mul_comm]

/-- The telescoped means tend to zero. -/
lemma tendsto_cesMean_shift_sub (x : BoundedSeq) :
    Filter.Tendsto (cesMean (shift x - x)) Filter.atTop (nhds 0) := by
  have e : cesMean (shift x - x) = (fun n => (x n - x 0) / (n : ℝ)) :=
    funext fun n => cesMean_shift_sub x n
  rw [e]
  refine squeeze_zero_norm (fun n => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat (2 * ‖x‖))
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hle : ‖x n - x 0‖ ≤ 2 * ‖x‖ := by
      calc ‖x n - x 0‖ ≤ ‖x n‖ + ‖x 0‖ := norm_sub_le _ _
        _ ≤ ‖x‖ + ‖x‖ := by
            gcongr <;>
              exact BoundedContinuousFunction.norm_coe_le_norm _ _
        _ = 2 * ‖x‖ := by ring
    calc ‖(x n - x 0) / (n : ℝ)‖
        = ‖x n - x 0‖ / ‖(n : ℝ)‖ := norm_div _ _
      _ ≤ (2 * ‖x‖) / ‖(n : ℝ)‖ := by gcongr
      _ = (2 * ‖x‖) / (n : ℝ) := by norm_num

/-- A continuous linear functional extending limits, positive and shift-invariant,
exists: the Hahn–Banach extension made continuous by `|L| ≤ ‖·‖`. -/
theorem exists_banachFunctional : ∃ L : BoundedSeq →L[ℝ] ℝ,
    (∀ x : BoundedSeq, ∀ a : ℝ, Filter.Tendsto (fun n => x n) Filter.atTop (nhds a) →
      L x = a) ∧
    (∀ x : BoundedSeq, (∀ n, 0 ≤ x n) → 0 ≤ L x) ∧
    (∀ x : BoundedSeq, L (shift x - x) = 0) := by
  refine ⟨LinearMap.mkContinuous extension 1 ?_, ?_, ?_, ?_⟩
  · intro x
    have h := extension_bound x
    simp only [one_mul]
    rwa [Real.norm_eq_abs]
  · intro x a h
    have hx : x ∈ convSub := ⟨a, h⟩
    have e1 : extension ((⟨x, hx⟩ : pmap.domain) : BoundedSeq) = pmap ⟨x, hx⟩ :=
      extension_eq_lim _
    have e2 : pmap (⟨x, hx⟩ : pmap.domain) = a :=
      tendsto_nhds_unique (Classical.choose_spec (⟨x, hx⟩ : pmap.domain).2) h
    have hyx : ((⟨x, hx⟩ : pmap.domain) : BoundedSeq) = x := rfl
    change extension x = a
    rw [← hyx, e1]
    exact e2
  · intro x h
    have hle : limsupCes (-x) ≤ 0 := by
      change Filter.limsup (cesMean (-x)) Filter.atTop ≤ _
      apply Filter.limsup_le_of_le (cesMeanCobdd (-x))
      apply Filter.Eventually.of_forall
      intro n
      rw [cesMean_neg]
      have hnn : 0 ≤ cesMean x n := by
        unfold cesMean
        apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
        exact Finset.sum_nonneg fun i _ => h i
      linarith
    have h2 : extension (-x) ≤ limsupCes (-x) := extension_le (-x)
    have hne : extension (-x) = -extension x := map_neg _ _
    change 0 ≤ extension x
    linarith [h2.trans hle]
  · intro x
    have hM0 : limsupCes (shift x - x) = 0 :=
      Filter.Tendsto.limsup_eq (tendsto_cesMean_shift_sub x)
    have hM0' : limsupCes (x - shift x) = 0 := by
      have e : cesMean (x - shift x) = (fun n => -cesMean (shift x - x) n) := by
        funext n
        show cesMean (x - shift x) n = -cesMean (shift x - x) n
        have esub : (x - shift x : BoundedSeq) = -((shift x - x) : BoundedSeq) := (neg_sub _ _).symm
        rw [esub, cesMean_neg]
      have htend : Filter.Tendsto (cesMean (x - shift x)) Filter.atTop (nhds 0) := by
        rw [e]
        simpa using (tendsto_cesMean_shift_sub x).neg
      exact Filter.Tendsto.limsup_eq htend
    have h1 : extension (shift x - x) ≤ limsupCes (shift x - x) := extension_le _
    have h2 : extension (x - shift x) ≤ limsupCes (x - shift x) := extension_le _
    rw [hM0] at h1
    rw [hM0'] at h2
    have hne : extension (x - shift x) = -extension (shift x - x) := by
      have e : (x - shift x : BoundedSeq) = -(shift x - x) := (neg_sub _ _).symm
      rw [e, map_neg]
    change extension (shift x - x) = 0
    linarith

end
end FunctionalAnalysis.BanachLimit
