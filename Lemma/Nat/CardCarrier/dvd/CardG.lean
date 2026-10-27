import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.GroupTheory.ClassBreadth
open ClassBreadth


namespace Definitions
end Definitions
namespace ClassBreadth

/--
[card_carrier_dvd_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean)
-/
@[path]
private lemma card_carrier_dvd_card
  [Group G] [Finite G]
  {g : G} :
-- imply
  Nat.card (ConjClasses.mk g).carrier ∣ Nat.card G := by
-- proof
  let := Fintype.ofFinite G
  classical
  have h : Nat.card (MulAction.orbit (ConjAct G) g) *
      Nat.card (MulAction.stabilizer (ConjAct G) g) = Nat.card (ConjAct G) := by
    simp only [Nat.card_eq_fintype_card]
    exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g
  rw [ConjAct.orbit_eq_carrier_conjClasses] at h
  have hG : Nat.card (ConjAct G) = Nat.card G :=
    Nat.card_congr ConjAct.ofConjAct.toEquiv
  rw [hG] at h
  exact ⟨_, h.symm⟩

end ClassBreadth

namespace ClassBreadth

/--
[exists_card_carrier_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean)
-/
@[path]
private lemma exists_card_carrier_eq_pow
  [Group G] [Finite G]
  {p : ℕ} [Fact p.Prime]
  {g : G}
-- given
  (hG : IsPGroup p G) :
-- imply
  ∃ k : ℕ, Nat.card (ConjClasses.mk g).carrier = p ^ k := by
-- proof
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  have hdvd : Nat.card (ConjClasses.mk g).carrier ∣ p ^ n := hn ▸ (card_carrier_dvd_card (g := g))
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
  exact ⟨k, hk⟩

end ClassBreadth

namespace ClassBreadth

/--
[elementBreadth_eq_of_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean)
-/
@[path]
private lemma elementBreadth_eq_of_card_eq
  [Group G] [Finite G]
  {p k : ℕ}
  {g : G}
-- given
  (hp : p.Prime)
  (h : Nat.card (ConjClasses.mk g).carrier = p ^ k) :
-- imply
  elementBreadth p g = k := by
-- proof
  rw [elementBreadth, h, Nat.log_pow hp.one_lt]

end ClassBreadth

namespace ClassBreadth

/--
[pow_elementBreadth_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean)
-/
@[path]
private lemma pow_elementBreadth_eq_card
  [Group G] [Finite G]
  {p : ℕ} [Fact p.Prime]
  {g : G}
-- given
  (hG : IsPGroup p G) :
-- imply
  p ^ elementBreadth p g = Nat.card (ConjClasses.mk g).carrier := by
-- proof
  obtain ⟨k, hk⟩ := exists_card_carrier_eq_pow (p := p) (g := g) hG
  rw [elementBreadth_eq_of_card_eq (g := g) Fact.out hk, hk]

end ClassBreadth

namespace ClassBreadth

/--
[carrier_mk_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean)
-/
@[path]
private lemma carrier_mk_one
  [Group G] :
-- imply
  (ConjClasses.mk (1 : G)).carrier = {1} := by
-- proof
  ext x
  simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]

end ClassBreadth

namespace ClassBreadth

/--
[elementBreadth_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean)
-/
@[path]
private lemma elementBreadth_one
  [Group G] [Finite G]
  {p : ℕ} :
-- imply
  elementBreadth p (1 : G) = 0 := by
-- proof
  rw [elementBreadth, carrier_mk_one, Nat.card_unique, Nat.log_one_right]

end ClassBreadth

namespace ClassBreadth

/--
[elementBreadth_le_breadth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean)
-/
@[path]
private lemma elementBreadth_le_breadth
  [Group G] [Fintype G]
  {p : ℕ}
  {g : G} :
-- imply
  elementBreadth p g ≤ breadth p G :=
-- proof
  Finset.le_sup (Finset.mem_univ g)

end ClassBreadth

namespace ClassBreadth

/--
[exists_breadth_eq_elementBreadth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassBreadth.lean)
-/
@[path]
private lemma exists_breadth_eq_elementBreadth
  [Group G] [Fintype G] [Nonempty G]
  {p : ℕ} :
-- imply
  ∃ g : G, breadth p G = elementBreadth p g := by
-- proof
  obtain ⟨g, -, hg⟩ := Finset.exists_mem_eq_sup Finset.univ
    Finset.univ_nonempty (fun g : G ↦ elementBreadth p g)
  exact ⟨g, hg⟩

end ClassBreadth


-- created on 2026-10-20
-- updated on 2026-10-26
