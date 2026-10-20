import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.Frobenius.Unique
open IsArithFrobAt


/--
[eq_of_inertia_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Unique.lean)
-/
@[path]
private lemma eq_of_inertia_eq_bot_eq
  [CommRing R] [CommRing S] [Algebra R S] [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
  {Q : Ideal S}
  {σ σ' : G}
-- given
  (hσ : IsArithFrobAt R σ Q)
  (hσ' : IsArithFrobAt R σ' Q)
  (hbot : Q.inertia G = ⊥) :
-- imply
  σ = σ' := by
-- proof
  apply IsArithFrobAt.eq_of_inertia_eq_bot hσ hσ' hbot

/--
[existsUnique_of_inertia_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/Unique.lean)
-/
@[path]
private lemma existsUnique_of_inertia_eq_bot_eq
  [CommRing R] [CommRing S] [Algebra R S] [Group G] [MulSemiringAction G S] [SMulCommClass G R S] [Finite G] [Algebra.IsInvariant R S G]
  {Q : Ideal S} [Q.IsPrime] [Finite (S ⧸ Q)]
  {σ σ' : G}
-- given
  (hbot : Q.inertia G = ⊥) :
-- imply
  ∃! σ : G, IsArithFrobAt R σ Q := by
-- proof
  apply IsArithFrobAt.existsUnique_of_inertia_eq_bot hbot


-- created on 2026-10-20
