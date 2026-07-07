import Lemma.Vector.Sum.eq.Zero
import Lemma.Vector.Dot.eq.Zero
import Lemma.Vector.EqCons_Tail
import Lemma.Vector.SumMapVal.eq.SumMap
open Vector


@[main]
private lemma main
  [Add β] [Zero β] [Mul β]
  {f₁ f₂ : α → β} :
-- imply
  ∀ {s : List.Vector α n}, (s.map fun x => f₁ x * f₂ x).sum = s.map f₁ ⬝ s.map f₂ := by
-- proof
  induction n with
  | zero =>
    simp [Dot.eq.Zero, Sum.eq.Zero]
  | succ n ih =>
    intro s
    rw [← SumMapVal.eq.SumMap (f := fun x => f₁ x * f₂ x)]
    have hval : s.val = s.head :: s.tail.val := by
      simpa using congrArg Subtype.val (EqCons_Tail s).symm
    rw [hval, List.map_cons, List.sum_cons]
    have h_dot₁ : s.map f₁ = f₁ s.head ::ᵥ s.tail.map f₁ := by
      rw [← EqCons_Tail s]
      apply List.Vector.map_cons
    have h_dot₂ : s.map f₂ = f₂ s.head ::ᵥ s.tail.map f₂ := by
      rw [← EqCons_Tail s]
      apply List.Vector.map_cons
    have : s.map f₁ ⬝ s.map f₂ = f₁ s.head * f₂ s.head + s.tail.map f₁ ⬝ s.tail.map f₂  := by
      rw [h_dot₁, h_dot₂]
      rfl
    rw [this]
    apply congr_arg₂ (· + ·) rfl ih


-- created on 2024-07-01
-- updated on 2025-02-23
