import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma subring_eq_top_of_inv_mem
  [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]
  (W : Subring K)
  (ϖ : V)
  -- given
  (hVW : ∀ v : V, algebraMap V K v ∈ W)
  (hϖ : Irreducible ϖ)
  (hinv : (algebraMap V K ϖ)⁻¹ ∈ W) :
  -- imply
  W = ⊤ := by
  -- proof
  refine eq_top_iff.mpr fun y _ => ?_
  if hy : y = 0 then
    rw [hy]
    apply W.zero_mem
  else
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hy
    rw [Units.smul_def, Algebra.smul_def]
    refine W.mul_mem (hVW _) ?_
    if hn : 0 ≤ n then
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [zpow_natCast, ← map_pow]
      apply hVW _
    else
      have hn : n < 0 := lt_of_not_ge hn
      obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
      rw [zpow_neg, zpow_natCast, ← inv_pow]
      apply W.pow_mem hinv m

private lemma exists_algebraMap_eq_of_mem_subring
  [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]
  (W : Subring K)
  (x : K)
  -- given
  (hVW : ∀ v : V, algebraMap V K v ∈ W)
  (hW : W ≠ ⊤)
  (hx : x ∈ W) :
  -- imply
  ∃ v : V, algebraMap V K v = x := by
  -- proof
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  if hx0 : x = 0 then
    refine ⟨0, by rw [map_zero, hx0]⟩
  else
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hx0
    have hinj := IsFractionRing.injective V K
    have hπ : algebraMap V K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
    have hu : algebraMap V K u ≠ 0 := (map_ne_zero_iff _ hinj).mpr u.ne_zero
    if hn : 0 ≤ n then
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      refine ⟨u * ϖ ^ m, by rw [map_mul, map_pow, Units.smul_def, Algebra.smul_def, zpow_natCast]⟩
    else
      exfalso
      have hn : n < 0 := lt_of_not_ge hn
      obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 :=
        Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hn)
      refine hW (subring_eq_top_of_inv_mem W ϖ hVW hϖ ?_)
      have key : (algebraMap V K ϖ)⁻¹ =
        (u • algebraMap V K ϖ ^ (-((k + 1 : ℕ) : ℤ))) * algebraMap V K (↑u⁻¹ * ϖ ^ k) := by
        rw [Units.smul_def, Algebra.smul_def, map_mul, map_pow, zpow_neg, zpow_natCast, map_units_inv]
        field_simp
        ring
      rw [key]
      apply W.mul_mem hx (hVW _)

/--
[IsDiscreteValuationRing_exists_algebraMap_eq_of_mem_subring_of_ne_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDiscreteValuationRing_exists_algebraMap_eq_of_mem_subring_of_ne_top.lean)
-/
@[path]
private lemma main
  [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]
  (W : Subring K)
  (x : K)
  -- given
  (hVW : ∀ v : V, algebraMap V K v ∈ W)
  (hW : W ≠ ⊤)
  (hx : x ∈ W) :
  -- imply
  ∃ v : V, algebraMap V K v = x :=
  exists_algebraMap_eq_of_mem_subring W x hVW hW hx


-- created on 2026-10-20
