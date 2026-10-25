/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiscreteFibers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.UniqueRetraction
import Lemma.Bijective.Any_And_In_Faces.is.Image.in.FacesAndEqImage.of.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.In_Apartments.In_Apartments
import Lemma.Finset.Any_And_All_EqAndAll_IsMaximalAndAll_EqImageSOrAdjacentAndAll_Eq.of.IsMaximal.In_Apartments
import Lemma.Finset.ImageRetractionMap.in.Faces.of.IsMaximal.In_Faces.In_Apartments
import Def.v1.Atlas.Buildings.code.AffineCoxeter.GeometricRealization.Part2
import Theorem.v1.Atlas.Buildings.code.Building.AptFoldingFromRetraction
import Def.v1.Atlas.Buildings.code.Building.AptIsoFixesIntersection
import Structure.v1.Atlas.Buildings.code.Building.DiscreteFibers
set_option linter.unusedSectionVars false


noncomputable section

open Finset BigOperators

namespace DiscreteFibers

variable {V : Type} [DecidableEq V]

/-- The open star of a point $x \in |\Delta|$: all points $z$ whose support
lies, together with the support of $x$, inside a single common face. -/
def star {Δ : SimplicialComplex V} (x : PointF Δ) : Set (PointF Δ) :=
  { z : PointF Δ | ∃ σ ∈ Δ.faces,
    (∀ v, x.wt v ≠ 0 → v ∈ σ) ∧ (∀ v, z.wt v ≠ 0 → v ∈ σ) }

/-- The pushforward of a weight function $\mathrm{wt}$ supported on $\sigma$
along a vertex map $\rho$: the new weight at $v$ is $\sum_{u \in \sigma,\,
\rho(u) = v} \mathrm{wt}(u)$. -/
noncomputable def retractionMapWt
    (ρ : V → V) (wt : V → ℝ) (σ : Finset V) : V → ℝ :=
  fun v => ∑ u ∈ σ, if ρ u = v then wt u else 0

/-- The $L^\infty$ distance between two barycentric points: the supremum of
$|p.\mathrm{wt}(v) - q.\mathrm{wt}(v)|$ over vertices in the union of their
supports. -/
noncomputable def dist {Δ : SimplicialComplex V} (p q : PointF Δ) : ℝ :=
  (p.face ∪ q.face).sup' (by
    have := p.wt_sum
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [Finset.union_eq_empty] at h
    simp [h.1] at this)
    (fun v => |p.wt v - q.wt v|)

end DiscreteFibers
end
