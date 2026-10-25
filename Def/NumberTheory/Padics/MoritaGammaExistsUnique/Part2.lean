/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/MoritaGammaExistsUnique.lean -/

import Def.NumberTheory.Padics.MoritaGamma
import Lemma.Nat.Padics.MoritaGamma
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular
import Theorem.NumberTheory.Padics.MoritaGammaExistsUnique
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
