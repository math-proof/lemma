import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic
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

abbrev BoundedSeq := ℕ →ᵇ ℝ

end
end FunctionalAnalysis.BanachLimit
