import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Logic.Basic

/-- `Minima[x:S](f(x))`: the infimum of `f` over `S`. -/
noncomputable def Minima [InfSet β] (S : Set α) (f : α → β) : β :=
  sInf (f '' S)

/-- `Maxima[x:S](f(x))`: the supremum of `f` over `S`. -/
noncomputable def Maxima [SupSet β] (S : Set α) (f : α → β) : β :=
  sSup (f '' S)

/-- `ArgMin[x:S](f(x))`: some minimizer of `f` on `S` (arbitrary when none exists). -/
noncomputable def ArgMin [Nonempty α] [Preorder β] (S : Set α) (f : α → β) : α :=
  Classical.epsilon fun x => x ∈ S ∧ ∀ y ∈ S, f x ≤ f y

/-- `ArgMax[x:S](f(x))`: some maximizer of `f` on `S` (arbitrary when none exists). -/
noncomputable def ArgMax [Nonempty α] [Preorder β] (S : Set α) (f : α → β) : α :=
  Classical.epsilon fun x => x ∈ S ∧ ∀ y ∈ S, f y ≤ f x


-- created on 2026-09-27
