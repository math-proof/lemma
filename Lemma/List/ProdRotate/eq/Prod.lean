import Theorem.List.Rotate.eq.AppendDrop__Take
import Lemma.List.Prod.eq.MulProdS
open List


/--
| attributes | lemma |
| :---: | :---: |
| path | List.ProdRotate.eq.Prod |
| comm | List.Prod.eq.ProdRotate |
-/
@[path, comm]
private lemma main
  [CommMonoid α]
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  (s.rotate i).prod = s.prod := by
-- proof
  rw [Rotate.eq.AppendDrop__Take]
  rw [Prod.eq.MulProdS.comm s (i % s.length)]
  simp


-- created on 2025-10-17
-- updated on 2026-11-20
