import Lemma.Vector.Sum.eq.Zero
import Lemma.Vector.SumCons.eq.Add_Sum
open Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Vector.MapSum.eq.SumMap.of.All_EqUFnAdd |
| comm | Vector.SumMap.eq.MapSum.of.All_EqUFnAdd |
-/
@[main, comm]
private lemma main
  [AddCommMonoid α]
  [AddCancelCommMonoid β]
  {f : α → β}
-- given
  (hf : ∀ a b, f (a + b) = f a + f b)
  (v : List.Vector α n) :
-- imply
  f v.sum = (v.map f).sum := by
-- proof
  induction v using List.Vector.inductionOn with
  | nil =>
    have h := hf 0 0
    have h₀ : f 0 = 0 := by grind
    simp [Sum.eq.Zero, h₀]
  | cons ih =>
    conv_rhs => rw [List.Vector.map_cons, SumCons.eq.Add_Sum]
    rw [SumCons.eq.Add_Sum, hf, ih]


-- created on 2026-07-29
