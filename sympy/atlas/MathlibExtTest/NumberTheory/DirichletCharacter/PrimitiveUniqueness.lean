/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/PrimitiveUniqueness.lean -/


import Lemma.Nat.DirichletCharacter.PrimitiveUniqueness


/-!
Abstract tests for uniqueness of the primitive inducer of a Dirichlet character.
-/

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R] {n : ℕ} [NeZero n]

-- A primitive inducer has the same conductor as the induced character.
example {d : ℕ} {χ' : DirichletCharacter R d}
    (χ : DirichletCharacter R n) (hprim : χ'.IsPrimitive)
    (hd : d ∣ n) (h : changeLevel hd χ' = χ) :
    χ'.conductor = χ.conductor := by
  have hlev : d = χ.conductor :=
    conductor_eq_of_isPrimitive_changeLevel χ hprim hd h
  have hprim' : χ'.conductor = d := hprim
  exact hprim'.trans hlev

-- Two inducers at the conductor level agree after transport.
example {d1 d2 : ℕ} {χ1 : DirichletCharacter R d1}
    {χ2 : DirichletCharacter R d2} (χ : DirichletCharacter R n)
    (hlev1 : d1 = χ.conductor) (hd1 : d1 ∣ n)
    (h1 : changeLevel hd1 χ1 = χ)
    (hlev2 : d2 = χ.conductor) (hd2 : d2 ∣ n)
    (h2 : changeLevel hd2 χ2 = χ) :
    hlev1 ▸ χ1 = hlev2 ▸ χ2 := by
  have e1 : hlev1 ▸ χ1 = χ.primitiveCharacter :=
    eq_primitiveCharacter_of_changeLevel_eq χ hlev1 hd1 h1
  have e2 : hlev2 ▸ χ2 = χ.primitiveCharacter :=
    eq_primitiveCharacter_of_changeLevel_eq χ hlev2 hd2 h2
  rw [e1, e2]

-- The packaged corollary supplies primitivity, induction, and uniqueness.
example {d : ℕ} {χ' : DirichletCharacter R d}
    (χ : DirichletCharacter R n) (hprim : χ'.IsPrimitive)
    (hd : d ∣ n) (h : changeLevel hd χ' = χ) :
    χ.primitiveCharacter.IsPrimitive ∧ FactorsThrough χ χ.conductor ∧
      d = χ.conductor := by
  obtain ⟨hP, hind, huniq⟩ := primitiveCharacter_isPrimitive_and_unique χ
  refine ⟨hP, ⟨_, _, hind.symm⟩, ?_⟩
  obtain ⟨hlev, _⟩ := huniq d χ' hprim hd h
  exact hlev

end DirichletCharacter
