import Mathlib.Order.ConditionallyCompleteLattice.Basic


/-- `Minima[x:S](f(x))`: the infimum of `f` over `S`. -/
noncomputable def Minima [InfSet β] (S : Set α) (f : α → β) : β :=
  sInf (f '' S)

/-- `Maxima[x:S](f(x))`: the supremum of `f` over `S`. -/
noncomputable def Maxima [SupSet β] (S : Set α) (f : α → β) : β :=
  sSup (f '' S)

/-- Underlying argmin: some minimizer of `f` on `S` (arbitrary when none exists).
Prefer the big-operator sugar `min⁻¹[i] e` / `min⁻¹[x ∈ S] e`. -/
noncomputable def «min⁻¹» [Nonempty α] [Preorder β] (S : Set α) (f : α → β) : α :=
  Classical.epsilon fun x => x ∈ S ∧ ∀ y ∈ S, f x ≤ f y

/-- Underlying argmax: some maximizer of `f` on `S` (arbitrary when none exists).
Prefer the big-operator sugar `max⁻¹[i] e` / `max⁻¹[x ∈ S] e`. -/
noncomputable def «max⁻¹» [Nonempty α] [Preorder β] (S : Set α) (f : α → β) : α :=
  Classical.epsilon fun x => x ∈ S ∧ ∀ y ∈ S, f y ≤ f x

