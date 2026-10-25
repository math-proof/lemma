/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/BanachLimit.lean -/

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Def.Analysis.FunctionalAnalysis.BanachLimit.Part3
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


namespace MathlibExt.Analysis.FunctionalAnalysis.BanachLimit

open scoped BoundedContinuousFunction

noncomputable section

/-- `limFun` is dominated by `limsupCes`: Cesàro means preserve limits. -/
lemma limFun_le (x : convSub) : limFun x ≤ limsupCes ↑x := by
  have h := Classical.choose_spec x.2
  have hces : Filter.Tendsto (cesMean ↑x) Filter.atTop (nhds (limFun x)) := h.cesaro
  have heq : Filter.limsup (cesMean ↑x) Filter.atTop = limFun x :=
    Filter.Tendsto.limsup_eq hces
  change limFun x ≤ Filter.limsup (cesMean ↑x) Filter.atTop
  rw [heq]

lemma pmap_le (x : pmap.domain) : pmap x ≤ limsupCes (x : BoundedSeq) :=
  limFun_le ⟨(x : BoundedSeq), x.2⟩

end
end MathlibExt.Analysis.FunctionalAnalysis.BanachLimit
