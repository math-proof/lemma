import sympy.sets.sets
import Lemma.Set.IffInS_Ico
open Set


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.All_UFnSub.is.All |
| comm | Bool.All.is.All_UFnSub |
| mp | Bool.All.of.All_UFnSub |
| mpr | Bool.All_UFnSub.of.All |
-/
@[main, comm, mp, mpr]
private lemma main
  {c a b : ℤ}
  {f : ℤ → Prop} :
-- imply
  (∀ i ∈ Ico (c - b + 1) (c - a + 1), f (c - i)) ↔ (∀ i ∈ Ico a b, f i) := by
-- proof
  constructor
  · intro h i hi
    simpa [sub_sub] using h (c - i) ((IffInS_Ico c a b i).mp hi)
  · intro h j hj
    exact h (c - j) ((IffInS_Ico c a b (c - j)).mpr (by simpa [sub_sub] using hj))


-- created on 2026-08-02
