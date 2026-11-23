/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Dynamics/EventuallyPeriodicSequence.lean -/
module

public import Abbrev.Dynamics.EventuallyPeriodicSequence
public import Theorem.Set.EventuallyPeriodicSequence
public import Mathlib.Data.ZMod.Defs

public section

namespace MetaMathlibExt

example {α : Type*} (a : α) : IsEventuallyPeriodic (fun _ : ℕ => a) :=
  IsEventuallyPeriodic.of_periodic (p := 1) (by decide) fun _ => rfl

example {α : Type*} {u : ℕ → α} :
    IsUltimatelyPeriodic u = IsEventuallyPeriodic u :=
  rfl

example : IsEventuallyPeriodic (fun n : ℕ => ((n : ℕ) : ZMod 3)) :=
  .of_finite_orbit (· + 1) _ fun n => Nat.cast_succ n

end MetaMathlibExt
