module
public import Mathlib.Data.Fintype.Basic
public import Instance.Order.StrictTotalOrder
public import Theorem.Set.StrictTotalOrder
public import Theorem.Set.SocialChoice.Arrow
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Push
public import Def.GameTheory.SocialChoice.Arrow.Part3
public import Def.GameTheory.SocialChoice.GibbardSatterthwaite.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/GibbardSatterthwaite.lean -/
section

namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

/-- The pair-raise does not depend on the order of the pair. -/
theorem raisePair_comm {Alt Voter : Type*} [DecidableEq Alt]
    (R : Profile Alt Voter) (a b : Alt) :
    raisePair R b a = raisePair R a b := by
  funext i
  unfold raisePair
  congr 1
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact or_comm

/-- The pair-raise preserves every comparison won by a pair member in the
triple-raise. Used for transitivity of the induced social order. -/
theorem triple_pair_preserve {Alt : Type*} [DecidableEq Alt]
    (o : StrictTotalOrder Alt) (a b c p q w d : Alt)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpq : p ≠ q)
    (hpsub : p = a ∨ p = b ∨ p = c) (hqsub : q = a ∨ q = b ∨ q = c)
    (hw : w = p ∨ w = q)
    (h : (raiseOrder o {a, b, c}).lt w d) : (raiseOrder o {p, q}).lt w d := by
  have hwP : w ∈ ({p, q} : Finset Alt) := by
    rcases hw with rfl | rfl <;> simp
  have hsub : ∀ z : Alt, z ∈ ({p, q} : Finset Alt) → z ∈ ({a, b, c} : Finset Alt) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    rcases hz with rfl | rfl
    · rcases hpsub with rfl | rfl | rfl <;> simp
    · rcases hqsub with rfl | rfl | rfl <;> simp
  have hwT : w ∈ ({a, b, c} : Finset Alt) := hsub w hwP
  by_cases hdw : d = w
  · rw [← hdw] at h
    exact absurd h ((raiseOrder o {a, b, c}).irrefl d)
  · by_cases hdP : d ∈ ({p, q} : Finset Alt)
    · have hdT : d ∈ ({a, b, c} : Finset Alt) := hsub d hdP
      have ho : o.lt w d :=
        (raise_preserve_inside o {a, b, c} hwT hdT).mp h
      exact (raise_preserve_inside o {p, q} hwP hdP).mpr ho
    · exact raise_mem_top o {p, q} hwP hdP

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted
end
