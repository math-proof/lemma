/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Labels.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.Basic
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments

open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- A labelling of a simplicial complex $K$ by a set $L$: a strict-monotone assignment of a finite,
nonempty set of labels to each face, monotone with respect to face inclusion. -/
structure Labelling (K : SimplicialComplex V) (L : Type*) [DecidableEq L] where
  labelMap : Finset V → Finset L
  label_nonempty : ∀ s ∈ K.faces, (labelMap s).Nonempty
  label_strictMono : ∀ s t, s ∈ K.faces → t ∈ K.faces →
    s ⊂ t → labelMap s ⊂ labelMap t

/-- A simplicial complex $K$ is *labellable* if there exists a labelling by some label type. -/
def SimplicialComplex.IsLabellable (K : SimplicialComplex V) : Prop :=
  ∃ (L : Type*) (_ : DecidableEq L), Nonempty (Labelling K L)

/-- Application of a labelling to a face: returns the label set assigned to $s$. -/
def Labelling.labelOf {K : SimplicialComplex V} {L : Type*} [DecidableEq L]
    (lab : Labelling K L) (s : Finset V) : Finset L :=
  lab.labelMap s

/-- Two chambers $C_1, C_2$ are $\ell$-*adjacent* (with respect to a labelling) if they are
adjacent and the label of their common face $C_1 \cap C_2$ equals $\ell$. -/
def LabelAdjacent {L : Type*} [DecidableEq L]
    (K : ChamberComplex V) (lab : Labelling K.toSimplicialComplex L)
    (ℓ : Finset L) (C₁ C₂ : Finset V) : Prop :=
  K.toSimplicialComplex.Adjacent C₁ C₂ ∧
    lab.labelMap (C₁ ∩ C₂) = ℓ

/-- A chamber complex is *uniquely labellable* if any two labellings differ by a bijection of label
sets, i.e. all labellings are canonical up to renaming of labels. -/
def ChamberComplex.IsUniquelyLabellable (K : ChamberComplex V) : Prop :=
  ∀ (L₁ L₂ : Type) [DecidableEq L₁] [DecidableEq L₂]
    (lab₁ : Labelling K.toSimplicialComplex L₁)
    (lab₂ : Labelling K.toSimplicialComplex L₂),
    ∃ f : L₁ → L₂, Function.Bijective f ∧
      ∀ s ∈ K.toSimplicialComplex.faces,
        lab₂.labelMap s = (lab₁.labelMap s).image f

/-- The *link* of a face $\sigma$ in $K$: the set of nonempty faces $\tau$ disjoint from $\sigma$
such that $\sigma \cup \tau$ is still a face of $K$. -/
def SimplicialComplex.link (K : SimplicialComplex V) (σ : Finset V)
    (_hσ : σ ∈ K.faces) : Set (Finset V) :=
  { τ : Finset V | τ.Nonempty ∧ Disjoint σ τ ∧ (σ ∪ τ) ∈ K.faces }
