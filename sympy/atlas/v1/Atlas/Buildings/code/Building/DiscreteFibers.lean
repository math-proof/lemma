/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/DiscreteFibers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.UniqueRetraction
import Lemma.Bijective.Any_And_In_Faces.is.Image.in.FacesAndEqImage.of.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.In_Apartments.In_Apartments
import Lemma.Finset.Any_And_All_EqAndAll_IsMaximalAndAll_EqImageSOrAdjacentAndAll_Eq.of.IsMaximal.In_Apartments
import Lemma.Finset.ImageRetractionMap.in.Faces.of.IsMaximal.In_Faces.In_Apartments
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.GeometricRealization
import sympy.atlas.v1.Atlas.Buildings.code.Building.AptFoldingFromRetraction
import sympy.atlas.v1.Atlas.Buildings.code.Building.AptIsoFixesIntersection

set_option linter.unusedSectionVars false

noncomputable section

open Finset BigOperators

/-- The simplicial complex consisting of all non-empty subsets of a fixed
chamber $C$ — the abstract closure of the simplex $C$. -/
def closureSC {V : Type} [DecidableEq V] (C : Finset V) (hC : C.Nonempty) :
    SimplicialComplex V where
  faces := { s : Finset V | s ⊆ C ∧ s.Nonempty }
  nonempty_of_mem := fun s hs => hs.2
  down_closed := fun {s t} hs ht hne => ⟨ht.trans hs.1, hne⟩

/-- A labelling-style retraction of a building $\mathcal{B}$ onto a chamber:
data of a base chamber $C$, a vertex map $\rho$ sending each face to a face
of $C$, injective on each face, and fixing $C$ pointwise. -/
structure LabellingRetraction {V : Type} [DecidableEq V] (b : Building V) where
  base : Finset V
  base_mem : base ∈ b.toChamberComplex.toSimplicialComplex.faces
  base_nonempty : base.Nonempty
  map : V → V
  map_face : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces,
    s.image map ⊆ base ∧ (s.image map).Nonempty
  map_injOn_face : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces,
    Set.InjOn map ↑s
  map_fixes_base : ∀ v ∈ base, map v = v

namespace DiscreteFibers

variable {V : Type} [DecidableEq V]

/-- A geometric point of the realisation $|\Delta|$ of a simplicial complex,
given as a barycentric weight function $\mathrm{wt} : V \to \mathbb{R}_{\geq 0}$
supported on a single face $\sigma$ with weights summing to $1$. -/
structure PointF (Δ : SimplicialComplex V) where
  wt : V → ℝ
  face : Finset V
  face_mem : face ∈ Δ.faces
  wt_nonneg : ∀ v, wt v ≥ 0
  wt_sum : ∑ v ∈ face, wt v = 1
  support_in_face : ∀ v, wt v ≠ 0 → v ∈ face

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

variable {V : Type} [DecidableEq V]
