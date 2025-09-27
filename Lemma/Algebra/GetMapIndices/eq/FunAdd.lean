import stdlib.List.Vector
import Lemma.Algebra.GetIndices.eq.Add
import Lemma.Vector.GetMap.eq.FunGet
import Lemma.Algebra.CoeAdd.eq.AddCoeS
open Algebra Vector


@[main]
private lemma main
-- given
  (f : ℕ → α)
  (j n : ℕ)
  (i : Fin ((⟨j, n + j, 1⟩ : Slice).length (n + j))) :
-- imply
  ((List.Vector.indices ⟨j, n + j, 1⟩ (n + j)).map fun i : Fin (n + j) => f i)[i] = f (i + j) := by
-- proof
  have := GetIndices.eq.Add j n i
  simp_all [GetMap.eq.FunGet]


@[main]
private lemma coe
-- given
  (f : ℕ → α)
  (j n : ℕ)
  (i : Fin ((⟨j, (n + j : ℕ), 1⟩ : Slice).length (n + j))) :
-- imply
  ((List.Vector.indices ⟨j, (n + j : ℕ), 1⟩ (n + j)).map fun i : Fin (n + j) => f i)[i] = f (i + j) := by
-- proof
  apply main


-- created on 2025-05-23
-- updated on 2025-05-27
