import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IsLocalRing_existsUnique_forall_eq_sum_smul_of_forall_coeff_mem_range](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_existsUnique_forall_eq_sum_smul_of_forall_coeff_mem_range.lean)
-/
@[path]
private lemma main
  {B : Type} [CommRing B] [IsLocalRing B]
  (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V] [Module B V] [IsScalarTower B (ResidueField B) V]
  (ι : V →ₗ[B] B) (hι : Function.Injective ι)
  {r : ℕ} (bV : Module.Basis (Fin r) (ResidueField B) V)
  {τ : Type} (Δ : MvPowerSeries τ B) (hΔ : ∀ n, MvPowerSeries.coeff n Δ ∈ LinearMap.range ι) :
  -- imply
  (∃! z : Fin r → MvPowerSeries τ (ResidueField B), ∀ zl : Fin r → MvPowerSeries τ B, (∀ i, MvPowerSeries.map (residue B) (zl i) = z i) → Δ = ∑ i, ι (bV i) • zl i) ∧ (∀ z : Fin r → MvPowerSeries τ (ResidueField B), ∃ zl : Fin r → MvPowerSeries τ B, ∀ i, MvPowerSeries.map (residue B) (zl i) = z i) := by
  -- proof
  classical
  have hv : ∀ n, ∃ v : V, ι v = MvPowerSeries.coeff n Δ := fun n => hΔ n
  choose v hv using hv
  have hcoeff : ∀ (zl : Fin r → MvPowerSeries τ B) (n : Finsupp τ ℕ), MvPowerSeries.coeff n (∑ i, ι (bV i) • zl i) = ι (∑ i, residue B (MvPowerSeries.coeff n (zl i)) • bV i) := by
    intro zl n
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPowerSeries.coeff_smul, show residue B (MvPowerSeries.coeff n (zl i)) • bV i = (MvPowerSeries.coeff n (zl i)) • bV i from IsScalarTower.algebraMap_smul (A := ResidueField B) (MvPowerSeries.coeff n (zl i)) (bV i), LinearMap.map_smul, smul_eq_mul, mul_comm]
  have hlift : ∀ z : Fin r → MvPowerSeries τ (ResidueField B), ∃ zl : Fin r → MvPowerSeries τ B, ∀ i, MvPowerSeries.map (residue B) (zl i) = z i := by
    intro z
    refine ⟨fun i n => Classical.choose (residue_surjective (z i n)), fun i => ?_⟩
    ext n
    rw [MvPowerSeries.coeff_map]
    apply Classical.choose_spec (residue_surjective (z i n))
  refine ⟨⟨fun i n => bV.repr (v n) i, ?_, ?_⟩, hlift⟩
  ·
    intro zl hzl
    ext n
    rw [hcoeff, ← hv n]
    congr 1
    have : ∀ i, residue B (MvPowerSeries.coeff n (zl i)) = bV.repr (v n) i := by
      intro i
      have := congrArg (MvPowerSeries.coeff n) (hzl i)
      rw [MvPowerSeries.coeff_map] at this
      refine this
    simp_rw [this]
    apply (bV.sum_repr (v n)).symm
  ·
    intro z hz
    obtain ⟨zl, hzl⟩ := hlift z
    have hΔ' := hz zl hzl
    funext i n
    have hn := congrArg (MvPowerSeries.coeff n) hΔ'
    rw [hcoeff, ← hv n] at hn
    have hvn := hι hn
    have : ∀ j, residue B (MvPowerSeries.coeff n (zl j)) = z j n := by
      intro j
      have := congrArg (MvPowerSeries.coeff n) (hzl j)
      rw [MvPowerSeries.coeff_map] at this
      refine this
    simp_rw [this] at hvn
    have := congrArg (fun w => bV.repr w i) hvn
    simp only [Module.Basis.repr_sum_self] at this
    apply this.symm


-- created on 2026-10-20
