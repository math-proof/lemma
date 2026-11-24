import Initialize.Tactic.Attr.Basic
import Lemma.Bool.All.of.All.limits.swap
import Lemma.Bool.All.of.All.limits.insert
import Lemma.Bool.All.of.All.limits.invert
import Lemma.Bool.All.of.All.limits.domain_defined.given
import Lemma.Bool.All.of.All.limits.domain_defined
import Lemma.Bool.All.of.All.limits.delete


@[path]
private lemma subst
  {A : Set ι}
  {n : ι → ℕ}
  {p : ι → ℕ → Prop}
-- given
  (h : ∀ i ∈ A, ∀ x < n i + 1, p i x) :
-- imply
  ∀ i ∈ A, p i (n i) :=
-- proof
  fun i hi => h i hi (n i) (Nat.lt_succ_self _)


-- created on 2024-06-25
