/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/IdentityProductNecklace.lean -/
module

public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.IdentityProductNecklace.Part3

public section

section

namespace MetaMathlibExt

/-- Shifting shrinks the orbit set. -/
lemma orbSet_mono (G : Type*) [Group G]
    (n : ℕ) [NeZero n] (k : ZMod n)
    (x : {x : Fin n → G // (List.ofFn x).prod = 1}) :
    orbSet G n (k +ᵥ x).val ⊆ orbSet G n x.val := by
  intro y hy
  obtain ⟨m, hmn, hm⟩ := hy
  refine ⟨(m + k.val) % n, Nat.mod_lt _ (NeZero.pos n), fun i => ?_⟩
  have h1 : y i = (k +ᵥ x).val ⟨(i.val + m) % n, Nat.mod_lt _ (NeZero.pos n)⟩ := hm _
  have h2 : ∀ j : Fin n, (k +ᵥ x).val j
      = x.val ⟨(j.val + k.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩ :=
    fun j => rfl
  rw [h1, h2]
  refine congrArg x.val (Fin.ext ?_)
  exact (mod_add_wrap i.val m k.val n).symm

/-- Shifting preserves the orbit set. -/
lemma orbSet_shift_eq (G : Type*) [Group G]
    (n : ℕ) [NeZero n] (k : ZMod n)
    (x : {x : Fin n → G // (List.ofFn x).prod = 1}) :
    orbSet G n (k +ᵥ x).val = orbSet G n x.val := by
  apply Set.Subset.antisymm (orbSet_mono G n k x)
  have hback : ((-k) +ᵥ (k +ᵥ x)) = x := by
    rw [← add_vadd, neg_add_cancel, zero_vadd]
  have hsub := orbSet_mono G n (-k) (k +ᵥ x)
  rwa [hback] at hsub

/-- Orbit sets respect the orbit relation. -/
lemma orbSet_congr (G : Type*) [Group G]
    (n : ℕ) [NeZero n]
    (x y : {x : Fin n → G // (List.ofFn x).prod = 1})
    (h : x ∈ AddAction.orbit (ZMod n) y) :
    orbSet G n x.val = orbSet G n y.val := by
  obtain ⟨g, hg⟩ := AddAction.mem_orbit_iff.mp h
  subst hg
  exact orbSet_shift_eq G n g y

end MetaMathlibExt
end
