import Lemma.Vector.Sum.eq.Zero
import Lemma.Vector.Dot.eq.Zero
import Lemma.Vector.Map.eq.Cons_MapTail
import Lemma.Vector.SumCons.eq.Add_Sum
import Lemma.Vector.DotConsS.eq.AddDotS
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
  -- Base case: n = 0
    simp [Dot.eq.Zero, Sum.eq.Zero]
  | succ n ih =>
  -- Inductive case: n = n + 1
    intro s
    rw [Map.eq.Cons_MapTail]
    rw [SumCons.eq.Add_Sum _ (List.Vector.map (fun x ↦ f₁ x * f₂ x) s.tail)]
    repeat rw [Map.eq.Cons_MapTail]
    rw [DotConsS.eq.AddDotS]
    rw [ih]


-- created on 2024-07-01
-- updated on 2025-02-23
