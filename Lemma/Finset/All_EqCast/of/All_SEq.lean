import Lemma.Finset.All_EqCast.of.All_SEq.Ne_Empty
import Lemma.Finset.NeUnivEmpty
open Finset


@[main]
private lemma main
  [AddCommMonoid α]
  {x : Fin m → List.Vector α n}
  {y : Fin m → List.Vector α n'}
-- given
  (h : ∀ i : Fin m, x i ≃ y i) :
-- imply
  ∀ i : Fin m, cast
    (by
      have h_n := (h i).left
      congr
    )
    (x i) = y i := by
-- proof
  intro i
  apply All_EqCast.of.All_SEq.Ne_Empty (s := Finset.univ)
  ·
    apply NeUnivEmpty i
  ·
    aesop
  ·
    aesop


-- created on 2025-11-05
-- updated on 2025-11-06
