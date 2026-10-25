/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Theorem.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part5


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
