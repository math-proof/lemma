module
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Choose.Sum
public import Theorem.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/
section

namespace MetaMathlibExt

open scoped BigOperators

instance finite_fixedNeZero_aux (d n : ℕ) [NeZero n] : Finite (fixedPolycube d n) :=
  Finite.of_injective (encodeSet_aux d n) (encodeSet_injective_aux d n)

instance fixedEmpty_aux (d : ℕ) : IsEmpty (fixedPolycube d 0) := by
  constructor
  intro P
  obtain ⟨S, ⟨hP, hn, _⟩⟩ := P
  obtain ⟨x0, _⟩ := hP.1
  have : S.card > 0 := Finset.card_pos.mpr ⟨x0, ‹x0 ∈ S›⟩
  omega

instance finite_fixed_aux (d n : ℕ) : Finite (fixedPolycube d n) := by
  by_cases hn : n = 0
  · subst hn
    have := fixedEmpty_aux d
    have := Fintype.ofIsEmpty (α := fixedPolycube d 0)
    exact Finite.of_fintype _
  · have : NeZero n := ⟨hn⟩
    exact finite_fixedNeZero_aux d n

instance finite_proper_aux (n i : ℕ) : Finite (properFixedPolycube n i) :=
  Finite.of_injective Subtype.val (fun _ _ h => Subtype.ext h)

end MetaMathlibExt
end
