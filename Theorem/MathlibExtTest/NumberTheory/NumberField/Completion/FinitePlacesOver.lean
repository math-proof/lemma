/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Completion/FinitePlacesOver.lean -/


import Instance.NumberTheory.NumberField.Completion.FinitePlacesOver
open IsDedekindDomain
open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
variable [Algebra K L] (v : HeightOneSpectrum (𝓞 K))


/-- The equivalence sends a place over `v` to its underlying prime ideal. -/
example (w : v.placesOver L) :
    v.placesOverEquivPrimesOver L w = ⟨w.val.asIdeal, w.val.isPrime, w.property⟩ :=
  rfl

/-- Round trip through the inverse of the equivalence. -/
example (Q : v.asIdeal.primesOver (𝓞 L)) :
    v.placesOverEquivPrimesOver L ((v.placesOverEquivPrimesOver L).symm Q) = Q :=
  (v.placesOverEquivPrimesOver L).apply_symm_apply Q

/-- Finiteness transfers to the places-over type. -/
example : Finite (v.placesOver L) := inferInstance

/-- Nonemptiness transfers to the places-over type. -/
example : Nonempty (v.placesOver L) := inferInstance

/-- Places-over cardinality agrees with the ambient `primesOver` cardinality. -/
example : Nat.card (v.placesOver L) = Nat.card (v.asIdeal.primesOver (𝓞 L)) :=
  Nat.card_congr (v.placesOverEquivPrimesOver L)

/-- The places-over cardinality is positive via the new `Nonempty` instance. -/
example : 0 < Nat.card (v.placesOver L) := Nat.card_pos

