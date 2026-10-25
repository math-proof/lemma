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
