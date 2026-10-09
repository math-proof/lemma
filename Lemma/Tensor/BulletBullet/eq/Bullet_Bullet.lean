import Lemma.Tensor.Bullet.eq.ProdODot__OPlusOTimes
import Lemma.Tensor.ODotODot.eq.ODot_ODot
import Lemma.Tensor.OPlusOPlus.eq.OPlus_OPlus
import Lemma.Tensor.OTimesOTimes.eq.OTimes_ODot
import Lemma.Tensor.OTimes_OPlus.eq.OPlusOTimesS
open Tensor

/--
http://shelf2.library.cmu.edu/Tech/23445461.pdf#page=15
-/
@[path]
private lemma main
  [OPlus α]
  [OTimes α]
  [ODot α]
  [Bullet α]
  {cᵢ c_j cₖ : α × α} :
-- imply
  (cᵢ • c_j) • cₖ = cᵢ • (c_j • cₖ) := by
-- proof
  rw [Bullet.eq.ProdODot__OPlusOTimes (c_j := c_j)]
  rw [Bullet.eq.ProdODot__OPlusOTimes (c_j := cₖ)]
  simp
  rw [ODotODot.eq.ODot_ODot]
  rw [OTimes_OPlus.eq.OPlusOTimesS]
  rw [OPlusOPlus.eq.OPlus_OPlus]
  rw [OTimesOTimes.eq.OTimes_ODot]
  rw [← Bullet.eq.ProdODot__OPlusOTimes (c_j := ⟨c_j.fst ⊙ cₖ.fst, (c_j.snd ⊗ cₖ.fst) ⊕ cₖ.snd⟩)]
  rw [← Bullet.eq.ProdODot__OPlusOTimes (c_j := cₖ)]


-- created on 2024-12-08
