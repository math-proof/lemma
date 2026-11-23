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

@[expose] public section

/-!
# Existence of Morita's p-adic gamma function
-/


section

namespace MetaMathlibExt

/-- The unit of `ZMod (p ^ (s+1))` attached to `k` with `¬ p ∣ k`. -/
noncomputable def unitOfNotDvd (p s k : ℕ) [Fact p.Prime] (hk : ¬ p ∣ k) :
    (ZMod (p ^ (s + 1)))ˣ :=
  ((ZMod.isUnit_natCast_iff_not_dvd_pow (p := p) (d := s + 1) (a := k) Fact.out
    (Nat.succ_pos s)).mpr hk).unit

/-- The gamma values on the dense range, as a function on the subtype. -/
noncomputable def moritaGammaPre (p : ℕ) [Fact p.Prime]
    (x : {x : PadicInt p // x ∈ Set.range ((↑) : ℕ → PadicInt p)}) : PadicInt p :=
  moritaGammaNat p (Function.invFun ((↑) : ℕ → PadicInt p) x.val)

end MetaMathlibExt
end
