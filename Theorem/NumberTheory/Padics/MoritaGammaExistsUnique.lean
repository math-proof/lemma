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
public import Def.NumberTheory.Padics.MoritaGammaExistsUnique

/-!
# Existence of Morita's p-adic gamma function
-/

public section


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
