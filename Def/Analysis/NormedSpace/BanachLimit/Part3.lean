import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Theorem.Analysis.NormedSpace.BanachLimit.Part2
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

/-- The subspace of convergent sequences. -/
def convSub : Submodule ℝ BoundedSeq :=
  { carrier := {x | ∃ a, Filter.Tendsto (fun n => x n) Filter.atTop (nhds a)}
    add_mem' := by
      rintro x y ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a + b, ha.add hb⟩
    zero_mem' := ⟨0, tendsto_const_nhds⟩
    smul_mem' := by
      rintro c x ⟨a, ha⟩
      exact ⟨c * a, ha.const_mul c⟩ }

/-- The limit functional on convergent sequences. -/
def limFun : convSub →ₗ[ℝ] ℝ where
  toFun x := Classical.choose (x.2 : ∃ a, _)
  map_add' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    have hx' := Classical.choose_spec hx
    have hy' := Classical.choose_spec hy
    have hadd := hx'.add hy'
    have hmem : x + y ∈ convSub := ⟨_, hadd⟩
    exact (tendsto_nhds_unique hadd (Classical.choose_spec hmem)).symm
  map_smul' := by
    rintro c ⟨x, hx⟩
    have hx' := Classical.choose_spec hx
    have hsm := hx'.const_mul c
    have hmem : c • x ∈ convSub := ⟨_, hsm⟩
    exact (tendsto_nhds_unique hsm (Classical.choose_spec hmem)).symm

/-- The limit functional as a partial linear map. -/
noncomputable def pmap : BoundedSeq →ₗ.[ℝ] ℝ := ⟨convSub, limFun⟩

end
end FunctionalAnalysis.BanachLimit
