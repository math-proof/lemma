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
import Def.NumberTheory.Padics.MoritaGammaExistsUnique
/-!
# Existence of Morita's p-adic gamma function
-/


section

namespace MetaMathlibExt

/-- The range inclusion has dense range. -/
lemma denseRange_subtype_val (p : ℕ) [Fact p.Prime] :
    DenseRange (Subtype.val :
      {x : PadicInt p // x ∈ Set.range ((↑) : ℕ → PadicInt p)} → PadicInt p) := by
  have h_range : Set.range (Subtype.val :
      {x : PadicInt p // x ∈ Set.range ((↑) : ℕ → PadicInt p)} → PadicInt p) =
      Set.range ((↑) : ℕ → PadicInt p) := by
    ext y
    simp only [Set.mem_range]
    constructor
    · rintro ⟨b, rfl⟩
      exact b.2
    · rintro ⟨n, rfl⟩
      exact ⟨⟨_, Set.mem_range_self n⟩, rfl⟩
  intro x
  rw [h_range]
  exact PadicInt.denseRange_natCast x

end MetaMathlibExt
end
