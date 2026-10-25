/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Frobenius/Unique.lean -/


import Theorem.RingTheory.Frobenius.Unique
import Lemma.Int.Frobenius.Unique
variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
  {Q : Ideal S} {σ σ' : G}


-- Uniqueness applies to any two Frobenius elements under trivial inertia.
example (hσ : IsArithFrobAt R σ Q) (hσ' : IsArithFrobAt R σ' Q)
    (hbot : Q.inertia G = ⊥) : σ = σ' :=
  IsArithFrobAt.eq_of_inertia_eq_bot hσ hσ' hbot

-- Existence-uniqueness delivers the witness together with its property.
example [Finite G] [Algebra.IsInvariant R S G]
    [Q.IsPrime] [Finite (S ⧸ Q)] (hbot : Q.inertia G = ⊥) :
    ∃! σ : G, IsArithFrobAt R σ Q :=
  IsArithFrobAt.existsUnique_of_inertia_eq_bot hbot

-- The unique witness itself satisfies the Frobenius predicate.
example [Finite G] [Algebra.IsInvariant R S G]
    [Q.IsPrime] [Finite (S ⧸ Q)] (hbot : Q.inertia G = ⊥) :
    IsArithFrobAt R
      (IsArithFrobAt.existsUnique_of_inertia_eq_bot (R := R) hbot).choose Q :=
  (IsArithFrobAt.existsUnique_of_inertia_eq_bot (R := R) hbot).choose_spec.1

