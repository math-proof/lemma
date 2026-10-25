/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.AffineMetric.Part5
import Lemma.Set.IsBoundedImage.of.IsBounded.IsSimilitude
import Lemma.Finset.AreOpposite.of.AreOpposite
import Lemma.Finset.ImageRetractionMap.in.Faces.of.IsMaximal.In_Faces.In_Apartments
import Def.v1.Atlas.Buildings.code.Building.Spherical
import Def.v1.Atlas.Buildings.code.Building.AptIsoFixesIntersection
import Structure.v1.Atlas.Buildings.code.Building.Infinity.Sectors
set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- Two sectors $S_1, S_2$ point in the same direction iff they have subsectors
$T_1 \subseteq S_1$ and $T_2 \subseteq S_2$ with $T_1.\text{vertices} = T_2.\text{vertices}$
— the parallelism relation underlying $X_\infty$ (Section 16.6). -/
def Sector.SameDirection (b : Building V) (S₁ S₂ : Sector b) : Prop :=
  ∃ (T₁ T₂ : Sector b),
    T₁.vertices ⊆ S₁.vertices ∧
    T₂.vertices ⊆ S₂.vertices ∧
    T₁.vertices = T₂.vertices

/-- A *direction*: the equivalence class of a sector under `SameDirection`, i.e. a
point of $X_\infty$ at the sector level. -/
def Sector.Direction (b : Building V) :=
  Quot (Sector.SameDirection b)

/-- $S'$ is a *subsector* of $S$: $S'.\text{vertices} \subseteq S.\text{vertices}$
and the two sectors share a direction. -/
def Sector.Subsector (b : Building V) (S' S : Sector b) : Prop :=
  S'.vertices ⊆ S.vertices ∧ Sector.SameDirection b S' S

/-- $S_1$ and $S_2$ are *opposite* sectors: same apartment, and they contain
subsectors sharing a common base vertex. -/
def Sector.IsOpposite (b : Building V) (S₁ S₂ : Sector b) : Prop :=
  S₁.apartment = S₂.apartment ∧
  ∃ (T₁ T₂ : Sector b),
    T₁.vertices ⊆ S₁.vertices ∧
    T₂.vertices ⊆ S₂.vertices ∧
    T₁.baseVertex = T₂.baseVertex

end AffineBuilding
