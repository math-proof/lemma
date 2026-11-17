/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.Module.PerfectSpace
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Uniformizable
/-!
# Sierpinski's characterization of the rationals
-/


section

public noncomputable section

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
