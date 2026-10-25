/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Topology.Perfect
import Mathlib.Topology.Instances.Rat
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Tactic.Linarith
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UniformSpace.Uniformizable
/-!
# Sierpinski's characterization of the rationals
-/


section

noncomputable section

open Set Filter

namespace MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted

/-- A block pairs corresponding clopen sets with optional matched points. -/
structure Block (X Y : Type*) where
  UX : Set X
  UY : Set Y
  pt : Option (X × Y)
  bound : ℕ

end MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted
end
end
