import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.Buildings.code.Building.FixedPointSubgroups
open Set FixedPointSubgroups


namespace FixedPointSubgroups

/--
[orbit_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/FixedPointSubgroups.lean)
-/
@[path]
lemma orbit_nonempty
  [Group Gt]
  [MetricSpace X]
  {act : IsometricAction Gt X}
  {K : Subgroup Gt}
  {x : X} :
-- imply
  (orbitSet act (K : Set Gt) x).Nonempty :=
-- proof
  ⟨x, 1, K.one_mem, act.smul_one x⟩

end FixedPointSubgroups

namespace FixedPointSubgroups

/--
[orbit_stable_restricted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/FixedPointSubgroups.lean)
-/
@[path]
lemma orbit_stable_restricted
  [Group Gt]
  [MetricSpace X]
  {act : IsometricAction Gt X}
  {K : Subgroup Gt}
  {x : X} :
-- imply
  (restrictIsometricAction act K).IsStable (orbitSet act (K : Set Gt) x) := by
-- proof
  intro ⟨g, hg⟩ y hy
  obtain ⟨k, hk, rfl⟩ := hy
  exact ⟨g * k, K.mul_mem hg hk, act.smul_mul g k x⟩

end FixedPointSubgroups

namespace FixedPointSubgroups

/--
[subgroup_le_stabilizer_of_restricted_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/FixedPointSubgroups.lean)
-/
@[path]
lemma subgroup_le_stabilizer_of_restricted_fixed
  [Group Gt]
  [MetricSpace X]
  {act : IsometricAction Gt X}
  {K : Subgroup Gt}
  {x₀ : X}
-- given
  (hfix : (restrictIsometricAction act K).IsFixedPoint x₀) :
-- imply
  K ≤ pointStabilizer act x₀ := by
-- proof
  intro g hg
  exact hfix ⟨g, hg⟩

end FixedPointSubgroups

namespace FixedPointSubgroups

/--
[stabilizer_orbit_eq_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/FixedPointSubgroups.lean)
-/
@[path]
lemma stabilizer_orbit_eq_singleton
  [Group Gt]
  [MetricSpace X]
  {act : IsometricAction Gt X}
  {x : X} :
-- imply
  orbitSet act (pointStabilizer act x : Set Gt) x = {x} := by
-- proof
  ext y
  constructor
  ·
    rintro ⟨g, hg, rfl⟩
    simp only [mem_singleton_iff]
    exact hg
  ·
    intro hy
    rw [mem_singleton_iff] at hy
    subst hy
    exact ⟨1, (pointStabilizer act y).one_mem, act.smul_one y⟩

end FixedPointSubgroups

namespace FixedPointSubgroups

/--
[born_bounded_orbit_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/FixedPointSubgroups.lean)
-/
@[path]
lemma born_bounded_orbit_bounded
  [Group Gt]
  [MetricSpace X]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {ctx : BuildingGroupContext Gt B_idx M}
  {E : Set Gt}
  {x : ctx.X}
-- given
  (hE : ctx.born.isBounded E) :
-- imply
  Bornology.IsBounded (orbitSet ctx.action E x) := by
-- proof
  have h_cp := ctx.born_bounded_orbit_at_chamber_point E hE
  obtain ⟨R, hR⟩ := h_cp.subset_closedBall ctx.chamber_point
  rw [Metric.isBounded_iff_subset_closedBall x]
  refine ⟨R + dist ctx.chamber_point x + dist ctx.chamber_point x, ?_⟩
  intro z hz
  obtain ⟨g, hg, rfl⟩ := hz
  simp only [Metric.mem_closedBall]
  have h1 : dist (ctx.action.smul g ctx.chamber_point) ctx.chamber_point ≤ R :=
    hR ⟨g, hg, rfl⟩
  have h_tri : dist (ctx.action.smul g ctx.chamber_point) x ≤
    dist (ctx.action.smul g ctx.chamber_point) ctx.chamber_point +
      dist ctx.chamber_point x := dist_triangle _ _ _
  calc dist (ctx.action.smul g x) x
    ≤ dist (ctx.action.smul g x) (ctx.action.smul g ctx.chamber_point) +
      dist (ctx.action.smul g ctx.chamber_point) x := dist_triangle _ _ _
    _ = dist x ctx.chamber_point +
      dist (ctx.action.smul g ctx.chamber_point) x :=
      by rw [(ctx.action.isometry_smul g).dist_eq]
    _ ≤ dist x ctx.chamber_point +
      (dist (ctx.action.smul g ctx.chamber_point) ctx.chamber_point +
        dist ctx.chamber_point x) := by linarith
    _ ≤ dist ctx.chamber_point x + (R + dist ctx.chamber_point x) := by
      rw [dist_comm x ctx.chamber_point]; linarith
    _ = R + dist ctx.chamber_point x + dist ctx.chamber_point x := by ring

end FixedPointSubgroups

namespace FixedPointSubgroups

/--
[orbit_bounded_born_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/FixedPointSubgroups.lean)
-/
@[path]
lemma orbit_bounded_born_bounded
  [Group Gt]
  [MetricSpace X]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {ctx : BuildingGroupContext Gt B_idx M}
  {E : Set Gt}
-- given
  (h : ∃ x : ctx.X, Bornology.IsBounded (orbitSet ctx.action E x)) :
-- imply
  ctx.born.isBounded E := by
-- proof
  obtain ⟨x, hx⟩ := h
  apply ctx.orbit_bounded_at_chamber_point_born_bounded
  obtain ⟨R, hR⟩ := hx.subset_closedBall x
  rw [Metric.isBounded_iff_subset_closedBall ctx.chamber_point]
  refine ⟨R + dist x ctx.chamber_point + dist x ctx.chamber_point, ?_⟩
  intro z hz
  obtain ⟨g, hg, rfl⟩ := hz
  simp only [Metric.mem_closedBall]
  have h1 : dist (ctx.action.smul g x) x ≤ R := by
    have := hR ⟨g, hg, rfl⟩
    simp only [Metric.mem_closedBall] at this
    exact this
  calc dist (ctx.action.smul g ctx.chamber_point) ctx.chamber_point
    ≤ dist (ctx.action.smul g ctx.chamber_point) (ctx.action.smul g x) +
      dist (ctx.action.smul g x) ctx.chamber_point := dist_triangle _ _ _
    _ = dist ctx.chamber_point x +
      dist (ctx.action.smul g x) ctx.chamber_point :=
      by rw [(ctx.action.isometry_smul g).dist_eq]
    _ ≤ dist ctx.chamber_point x +
      (dist (ctx.action.smul g x) x + dist x ctx.chamber_point) := by
      linarith [dist_triangle (ctx.action.smul g x) x ctx.chamber_point]
    _ ≤ dist x ctx.chamber_point + (R + dist x ctx.chamber_point) := by
      rw [dist_comm ctx.chamber_point x]; linarith
    _ = R + dist x ctx.chamber_point + dist x ctx.chamber_point := by ring

end FixedPointSubgroups

namespace FixedPointSubgroups

/--
[stabilizer_maximal_born_ax](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/FixedPointSubgroups.lean)
-/
@[path]
lemma stabilizer_maximal_born_ax
  [Group Gt]
  [MetricSpace X]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {ctx : BuildingGroupContext Gt B_idx M}
  {x : ctx.X}
  {H : Subgroup Gt} :
-- imply
  pointStabilizer ctx.action x < H → ¬ctx.born.isBounded (H : Set Gt) := by
-- proof
  intro hlt hbdd
  have h_orbit_bdd : Bornology.IsBounded (orbitSet ctx.action (H : Set Gt) x) :=
    born_bounded_orbit_bounded ctx (H : Set Gt) hbdd x
  have h_le : H ≤ pointStabilizer ctx.action x :=
    ctx.stabilizer_of_bounded_orbit x H hlt.le h_orbit_bdd
  exact absurd (le_antisymm hlt.le h_le) (ne_of_lt hlt)

end FixedPointSubgroups

namespace FixedPointSubgroups

/--
[decomp_stable_in_stabilizer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/FixedPointSubgroups.lean)
-/
@[path]
lemma decomp_stable_in_stabilizer
  [Group Gt]
  [MetricSpace X]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {ctx : BuildingGroupContext Gt B_idx M}
  {K : Subgroup Gt}
  {σ : Gt}
  {g : Gt}
  {k : Gt}
-- given
  (hK : CompactSubgroups.IsMaximalBounded ctx.born K)
  (hσ : σ ∈ ctx.gbnpair.Tt)
  (_hg : g ∈ ctx.gbnpair.G)
  (hk : k ∈ K)
  (hk_eq : k = σ * g) :
-- imply
  g ∈ K := by
-- proof
  have hσ_K : σ ∈ K := ctx.Tt_in_every_maximal_bounded K hK σ hσ
  have hg_eq : g = σ⁻¹ * k := by
    rw [hk_eq]; group
  rw [hg_eq]
  exact K.mul_mem (K.inv_mem hσ_K) hk

end FixedPointSubgroups

namespace FixedPointSubgroups

/--
[stabilizer_born_bounded_thm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/FixedPointSubgroups.lean)
-/
@[path]
lemma stabilizer_born_bounded_thm
  [Group Gt]
  [MetricSpace X]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {ctx : BuildingGroupContext Gt B_idx M}
  {x : ctx.X} :
-- imply
  ctx.born.isBounded (pointStabilizer ctx.action x : Set Gt) := by
-- proof
  apply orbit_bounded_born_bounded ctx
  refine ⟨x, ?_⟩
  rwa [stabilizer_orbit_eq_singleton]

end FixedPointSubgroups

namespace FixedPointSubgroups

/--
[orbit_bounded_implies_action_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/FixedPointSubgroups.lean)
-/
@[path]
lemma orbit_bounded_implies_action_bounded
  [Group Gt]
  [MetricSpace X]
  [Group Gt]
  [MetricSpace X]
  {act : IsometricAction Gt X}
  {E : Set Gt}
  {x₀ : X}
  {Y : Set X}
-- given
  (h_orbit_bdd : Bornology.IsBounded (orbitSet act E x₀))
  (hY : Bornology.IsBounded Y) :
-- imply
  Bornology.IsBounded (actionOnSet act E Y) := by
-- proof
  obtain ⟨δ, hδ⟩ := h_orbit_bdd.subset_closedBall x₀
  obtain ⟨D, hD⟩ := hY.subset_closedBall x₀
  rw [Metric.isBounded_iff_subset_closedBall x₀]
  refine ⟨δ + D, ?_⟩
  intro z hz
  obtain ⟨g, hg, y, hy, rfl⟩ := hz
  simp only [Metric.mem_closedBall] at *
  have h1 : dist (act.smul g x₀) x₀ ≤ δ := hδ ⟨g, hg, rfl⟩
  have h2 : dist y x₀ ≤ D := hD hy
  calc dist (act.smul g y) x₀
    ≤ dist (act.smul g y) (act.smul g x₀) + dist (act.smul g x₀) x₀ := dist_triangle _ _ _
    _ = dist y x₀ + dist (act.smul g x₀) x₀ := by rw [(act.isometry_smul g).dist_eq]
    _ ≤ D + δ := by linarith
    _ = δ + D := by ring

end FixedPointSubgroups

namespace FixedPointSubgroups

/--
[actionOnSet_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/FixedPointSubgroups.lean)
-/
@[path]
lemma actionOnSet_singleton
  [Group Gt]
  [MetricSpace X]
  {act : IsometricAction Gt X}
  {E : Set Gt}
  {x : X} :
-- imply
  actionOnSet act E {x} = orbitSet act E x := by
-- proof
  ext z
  simp only [actionOnSet, orbitSet, mem_setOf_eq, mem_singleton_iff]
  constructor
  · rintro ⟨g, hg, y, rfl, heq⟩; exact ⟨g, hg, heq⟩
  · rintro ⟨g, hg, heq⟩; exact ⟨g, hg, x, rfl, heq⟩

end FixedPointSubgroups

namespace FixedPointSubgroups

/--
[BoundedSubsetsEquivalence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/FixedPointSubgroups.lean)
-/
@[path]
lemma BoundedSubsetsEquivalence
  [Group Gt]
  [MetricSpace X]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {ctx : BuildingGroupContext Gt B_idx M}
  {E : Set Gt} :
-- imply
  (ctx.born.isBounded E → ∀ x : ctx.X, Bornology.IsBounded (orbitSet ctx.action E x)) ∧ ((∃ x : ctx.X, Bornology.IsBounded (orbitSet ctx.action E x)) → ∀ Y : Set ctx.X, Bornology.IsBounded Y → Bornology.IsBounded (actionOnSet ctx.action E Y)) ∧ ((∀ Y : Set ctx.X, Bornology.IsBounded Y → Bornology.IsBounded (actionOnSet ctx.action E Y)) → ctx.born.isBounded E) := by
-- proof
  refine ⟨?_, ?_, ?_⟩
  ·
    exact born_bounded_orbit_bounded ctx E
  ·
    intro ⟨x₀, hx₀⟩ Y hY
    exact orbit_bounded_implies_action_bounded ctx.action E x₀ hx₀ Y hY
  ·
    intro h_all_bounded
    apply orbit_bounded_born_bounded ctx
    obtain ⟨x₀⟩ := ctx.nonempty
    refine ⟨x₀, ?_⟩
    rw [← actionOnSet_singleton]
    exact h_all_bounded {x₀} Bornology.isBounded_singleton

end FixedPointSubgroups

namespace FixedPointSubgroups

/--
[stabilizer_is_maximal_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/FixedPointSubgroups.lean)
-/
@[path]
lemma stabilizer_is_maximal_bounded
  [Group Gt]
  [MetricSpace X]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {ctx : BuildingGroupContext Gt B_idx M}
  {x₀ : ctx.X} :
-- imply
  CompactSubgroups.IsMaximalBounded ctx.born (pointStabilizer ctx.action x₀) := by
-- proof
  constructor
  ·
    exact stabilizer_born_bounded_thm ctx x₀
  ·
    exact stabilizer_maximal_born_ax ctx x₀

end FixedPointSubgroups

namespace FixedPointSubgroups

/--
[stabilizer_Gt_decomp_mem_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/FixedPointSubgroups.lean)
-/
@[path]
lemma stabilizer_Gt_decomp_mem_right
  [Group Gt]
  [MetricSpace X]
  [Group Gt]
  [Fintype B_idx]
  [DecidableEq B_idx]
  {M : CoxeterMatrix B_idx}
  {ctx : BuildingGroupContext Gt B_idx M}
  {K : Subgroup Gt}
  {σ : Gt}
  {g : Gt}
  {k : Gt}
-- given
  (hK : CompactSubgroups.IsMaximalBounded ctx.born K)
  (hσ : σ ∈ ctx.gbnpair.Tt)
  (hg : g ∈ ctx.gbnpair.G)
  (hk : k ∈ K)
  (hk_eq : k = σ * g) :
-- imply
  g ∈ K :=
-- proof
  decomp_stable_in_stabilizer ctx K hK σ hσ g hg k hk hk_eq

end FixedPointSubgroups


-- created on 2026-10-23
