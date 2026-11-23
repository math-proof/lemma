/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean -/

module

public import Def.NumberTheory.Padics.MoritaGamma
public import Theorem.Nat.Padics.MoritaGamma
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Separation.CompletelyRegular
public import Theorem.NumberTheory.Padics.MoritaGammaExistsUnique

@[expose] public section

/-!
# Existence of Morita's p-adic gamma function
-/


section

namespace MetaMathlibExt

/-- The continuous extension of the gamma values to all of `PadicInt p`. -/
noncomputable def moritaGammaExtend (p : ℕ) [Fact p.Prime] (_hp2 : p ≠ 2) :
    PadicInt p → PadicInt p :=
  IsDenseInducing.extend
    (IsUniformInducing.isDenseInducing isUniformEmbedding_subtype_val.isUniformInducing
      (denseRange_subtype_val p))
    (moritaGammaPre p)

end MetaMathlibExt
end
