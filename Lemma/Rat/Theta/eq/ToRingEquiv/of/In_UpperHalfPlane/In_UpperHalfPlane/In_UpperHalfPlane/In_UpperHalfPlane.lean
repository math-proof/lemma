import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.CerednikDrinfeld.DrinfeldHolomorphic
open scoped MatrixGroups
open CerednikDrinfeld.Omega


private lemma continuous_toRingEquiv {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] (s : IsometricAut K₀ K) : Continuous s.toRingEquiv := by
  apply continuous_of_continuousAt_zero s.toRingEquiv
  unfold ContinuousAt
  rw [map_zero, (Valued.hasBasis_nhds_zero K Γ₀).tendsto_iff (Valued.hasBasis_nhds_zero K Γ₀)]
  intro γ _
  refine ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq] at hx ⊢
  apply lt_of_eq_of_lt (s.vRestrict_map x) hx

namespace Definitions
end Definitions

/--
[CerednikDrinfeld_Omega_theta_isometricAut](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_Omega_theta_isometricAut.lean)
-/
@[path]
private lemma main
  [Field K₀] [Field K] [Algebra K₀ K] [DecidableEq K] [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [Group G]
  {ρ : G →* Matrix.ProjGenLinGroup (Fin 2) K₀}
  {s : IsometricAut K₀ K}
  {a b z₀ z : K}
-- given
  (ha : a ∈ upperHalfPlane K₀ K)
  (hb : b ∈ upperHalfPlane K₀ K)
  (_ : z₀ ∈ upperHalfPlane K₀ K)
  (_ : z ∈ upperHalfPlane K₀ K) :
-- imply
  theta ρ (s.toRingEquiv a) (s.toRingEquiv b) (s.toRingEquiv z₀) (s.toRingEquiv z) =
      s.toRingEquiv (theta ρ a b z₀ z) := by
-- proof
  have hcont : Continuous s.toRingEquiv := continuous_toRingEquiv s
  have hcont' : Continuous s.toRingEquiv.symm := by
    have h := continuous_toRingEquiv s⁻¹
    rwa [IsometricAut.inv_toRingEquiv] at h
  unfold theta
  rw [Function.LeftInverse.map_tprod (thetaFactor ρ a b z₀ z) hcont hcont' s.toRingEquiv.symm_apply_apply]
  refine tprod_congr fun γ => ?_
  unfold thetaFactor crossRatio
  rw [map_div₀, map_mul, map_mul, map_sub, map_sub, map_sub, map_sub, s.comm_pmoebius _ ha, s.comm_pmoebius _ hb]


-- created on 2026-10-24
