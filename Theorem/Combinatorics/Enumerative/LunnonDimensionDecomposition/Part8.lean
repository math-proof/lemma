/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Def.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part9


section

namespace MetaMathlibExt

open scoped BigOperators

lemma fiberToProper_explicit_aux (d n : ℕ) (A : Finset (Fin d))
    (S : Finset (latticeCell d))
    (hP : isPolycubeCells d S) (hnS : S.card = n) (hC : isCanonicalCells d S)
    (hsup : supportFinset_aux d S = A)
    (hz : ∀ x ∈ S, ∀ k : Fin d, k ∉ A → x k = 0) :
    fiberToProper_aux d n A ⟨⟨S, hP, hnS, hC⟩, hsup⟩ =
      (⟨⟨compressSet_aux2 d A S,
        conn_compressSet_aux d A S hP hz,
        by rw [card_compressSet_aux d A S hz, hnS],
        canon_compressSet_aux d A S hC⟩,
      by rw [properDimension_eq_support_aux, support_compressSet_aux d A S hsup,
        Finset.card_univ, Fintype.card_fin]⟩ :
      properFixedPolycube n A.card) := rfl

lemma properToFiber_explicit_aux (d n : ℕ) (A : Finset (Fin d))
    (T : Finset (latticeCell A.card))
    (hPT : isPolycubeCells A.card T) (hnT : T.card = n)
    (hCT : isCanonicalCells A.card T)
    (hproper : properDimension A.card T = A.card) :
    properToFiber_aux d n A ⟨⟨T, hPT, hnT, hCT⟩, hproper⟩ =
      (⟨⟨expandSet_aux2 d A T,
        conn_expandSet_aux d A T hPT,
        by rw [card_expandSet_aux d A T, hnT],
        canon_expandSet_aux d A T hPT.1 hCT⟩,
      support_expandSet_aux d A T (by
        have h1 : (supportFinset_aux A.card T).card = Fintype.card (Fin A.card) := by
          rw [← properDimension_eq_support_aux, hproper, Fintype.card_fin]
        exact Finset.eq_univ_of_card _ h1)⟩ :
      fiberSet_aux d n A) := rfl

end MetaMathlibExt
end
