import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Sidorenko.Part2
open SimpleGraph Finset BigOperators BlakleyRoy


namespace BlakleyRoy

/--
[pathGraph4_adj_cases](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Sidorenko.lean)
-/
@[path]
lemma pathGraph4_adj_cases
  {x y : Fin 4}
-- given
  (h : (pathGraph 4).Adj x y) :
-- imply
  (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨ (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) := by
-- proof
  simp only [pathGraph, hasse_adj, Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at h
  omega

end BlakleyRoy

namespace BlakleyRoy

/--
[nat_card_hom_eq_walkCount](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Sidorenko.lean)
-/
@[path]
lemma nat_card_hom_eq_walkCount
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  Nat.card (pathGraph 4 →g G) = walkCount G := by
-- proof
  rw [Nat.card_eq_fintype_card, walkCount]
  have equiv : (pathGraph 4 →g G) ≃
    (Σ b : V, Σ c : ↥(G.neighborFinset b),
      ↥(G.neighborFinset b) × ↥(G.neighborFinset c.val)) := {
    toFun := fun φ =>
      have h12 : G.Adj (φ 1) (φ 2) := φ.map_rel' (by
        show (pathGraph 4).Adj 1 2
        rw [pathGraph, hasse_adj, Fin.covBy_iff, Nat.covBy_iff_add_one_eq]; left; norm_num)
      have h01 : G.Adj (φ 0) (φ 1) := φ.map_rel' (by
        show (pathGraph 4).Adj 0 1
        rw [pathGraph, hasse_adj, Fin.covBy_iff, Nat.covBy_iff_add_one_eq]; left; norm_num)
      have h23 : G.Adj (φ 2) (φ 3) := φ.map_rel' (by
        show (pathGraph 4).Adj 2 3
        rw [pathGraph, hasse_adj, Fin.covBy_iff, Nat.covBy_iff_add_one_eq]; left; norm_num)
      ⟨φ 1, ⟨φ 2, (G.mem_neighborFinset (φ 1) (φ 2)).mpr h12⟩,
        ⟨φ 0, (G.mem_neighborFinset (φ 1) (φ 0)).mpr h01.symm⟩,
        ⟨φ 3, (G.mem_neighborFinset (φ 2) (φ 3)).mpr h23⟩⟩
    invFun := fun ⟨b, ⟨c, hc⟩, ⟨a, ha⟩, ⟨d, hd⟩⟩ => {
      toFun := fun i => match i with | 0 => a | 1 => b | 2 => c | 3 => d
      map_rel' := fun {x y} hxy => by
        have ha' : G.Adj a b := ((G.mem_neighborFinset b a).mp ha).symm
        have hc' : G.Adj b c := (G.mem_neighborFinset b c).mp hc
        have hd' : G.Adj c d := (G.mem_neighborFinset c d).mp hd
        rcases pathGraph4_adj_cases hxy with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ha'
        · exact ha'.symm
        · exact hc'
        · exact hc'.symm
        · exact hd'
        · exact hd'.symm
    }
    left_inv := fun φ => by
      ext i
      match i with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
      | ⟨3, _⟩ => rfl
    right_inv := fun ⟨_, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  }
  rw [Fintype.card_congr equiv, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_coe]
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_coe_sort (G.neighborFinset b) (fun c => (G.neighborFinset c).card)
/-- Cauchy-Schwarz-type bound: $(\sum_v \deg v)(\sum_v \deg^2 v) \le |V| \cdot W(G)$ where
$W(G)$ is the walk count. A key step in proving Blakey-Roy for $P_4$. -/

end BlakleyRoy


-- created on 2026-10-23
