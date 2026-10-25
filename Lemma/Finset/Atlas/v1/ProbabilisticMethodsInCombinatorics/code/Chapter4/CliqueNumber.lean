import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.CliqueNumber.Part2
open Finset BigOperators Filter Topology CliqueNumber
open scoped Classical


namespace CliqueNumber

/--
[expectedKCliques_eq_div](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/CliqueNumber.lean)
-/
@[path]
lemma expectedKCliques_eq_div
  {n k : ℕ} :
-- imply
  expectedKCliques n k = (n.choose k : ℝ) / (2 : ℝ) ^ (k.choose 2) := by
-- proof
  unfold expectedKCliques
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv]

end CliqueNumber

namespace CliqueNumber

/--
[probCliqueGe_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/CliqueNumber.lean)
-/
@[path]
lemma probCliqueGe_nonneg
  {n k : ℕ} :
-- imply
  0 ≤ probCliqueGe n k := by
-- proof
  unfold probCliqueGe; positivity

end CliqueNumber

namespace CliqueNumber

/--
[card_eq_Iic_mul_Ici](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/CliqueNumber.lean)
-/
@[path]
lemma card_eq_Iic_mul_Ici
  [BooleanAlgebra α]
  [Fintype α]
  {a : α} :
-- imply
  Fintype.card α = Fintype.card (Set.Iic a) * Fintype.card (Set.Ici a) := by
-- proof
  conv_rhs => rw [Fintype.card_congr (iciEquivIicCompl a)]
  rw [← Fintype.card_prod]
  exact Fintype.card_congr (boolAlgDecomp a)

end CliqueNumber

namespace CliqueNumber

/--
[card_Iic_eq_pow_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/CliqueNumber.lean)
-/
@[path]
lemma card_Iic_eq_pow_edgeFinset
  [Fintype V]
  [DecidableEq V]
  {a : SimpleGraph V} :
-- imply
  Fintype.card (Set.Iic a) = 2 ^ a.edgeFinset.card := by
-- proof
  rw [Fintype.card_congr (iicEquivBoolFn a)]
  simp [Fintype.card_bool]
set_option maxHeartbeats 600000 in

end CliqueNumber

namespace CliqueNumber

/--
[markov_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/CliqueNumber.lean)
-/
@[path]
lemma markov_bound
  {n k : ℕ} :
-- imply
  probCliqueGe n k ≤ expectedKCliques n k := by
-- proof
  unfold probCliqueGe
  rw [expectedKCliques_eq_div]
  have htotal_pos : (0 : ℝ) < (Fintype.card (SimpleGraph (Fin n)) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ (k.choose 2) := by positivity
  rw [div_le_div_iff₀ htotal_pos h2pow_pos]
  suffices hnat : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => ¬G.CliqueFree k)).card *
    2 ^ (k.choose 2) ≤ n.choose k * Fintype.card (SimpleGraph (Fin n)) by
    exact_mod_cast hnat
  let completeOn (s : Finset (Fin n)) : SimpleGraph (Fin n) :=
    ⟨fun u v => u ∈ s ∧ v ∈ s ∧ u ≠ v,
      fun _ _ ⟨hu, hv, huv⟩ => ⟨hv, hu, huv.symm⟩, ⟨fun _ h => h.2.2 rfl⟩⟩
  have hunion : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => ¬G.CliqueFree k)).card ≤
    ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      (Finset.univ.filter (fun G : SimpleGraph (Fin n) => completeOn s ≤ G)).card := by
    apply le_trans (Finset.card_le_card _) Finset.card_biUnion_le
    intro G hG
    rw [Finset.mem_filter] at hG
    rw [Finset.mem_biUnion]
    have hncf := hG.2
    rw [SimpleGraph.CliqueFree] at hncf
    push Not at hncf
    obtain ⟨s, hs⟩ := hncf
    refine ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hs.card_eq⟩, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun u v ⟨hu, hv, huv⟩ => hs.isClique hu hv huv⟩
  have hIci_bound : ∀ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
    (Finset.univ.filter (fun G : SimpleGraph (Fin n) => completeOn s ≤ G)).card *
      2 ^ (k.choose 2) ≤ Fintype.card (SimpleGraph (Fin n)) := by
    intro s hs
    have hscard : s.card = k := (Finset.mem_powersetCard.mp hs).2
    have hfilt_eq : (Finset.univ.filter (fun G : SimpleGraph (Fin n) => completeOn s ≤ G)).card =
      Fintype.card (Set.Ici (completeOn s)) := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (by
        intro G; simp [Finset.mem_filter, Set.mem_Ici]))
    rw [hfilt_eq]
    have hdecomp := card_eq_Iic_mul_Ici (completeOn s)
    have hIic := card_Iic_eq_pow_edgeFinset (completeOn s)
    calc Fintype.card (Set.Ici (completeOn s)) * 2 ^ k.choose 2
      ≤ Fintype.card (Set.Ici (completeOn s)) * Fintype.card (Set.Iic (completeOn s)) := by
        apply Nat.mul_le_mul_left
        rw [hIic]
        apply Nat.pow_le_pow_right (by norm_num)
        rw [← hscard]
        have : s.card.choose 2 ≤ Fintype.card ↑(completeOn s).edgeSet := by
          rw [show s.card.choose 2 = Fintype.card {e : Sym2 ↥s // ¬e.IsDiag} from by
            rw [Sym2.card_subtype_not_diag, Fintype.card_coe]]
          exact Fintype.card_le_of_injective
            (fun (e : {e : Sym2 ↥s // ¬e.IsDiag}) =>
              (⟨Sym2.map (Subtype.val) e.1, by
                have hnd := e.2
                revert hnd
                refine Sym2.ind (fun a b hnd => ?_) e.1
                simp only [Sym2.map_mk, SimpleGraph.mem_edgeSet, completeOn]
                exact ⟨a.2, b.2, fun h => hnd (Sym2.mk_isDiag_iff.mpr (Subtype.ext h))⟩
              ⟩ : ↑(completeOn s).edgeSet))
            (fun ⟨e1, he1⟩ ⟨e2, he2⟩ heq => by
              simp only [Subtype.mk.injEq] at heq
              exact Subtype.ext (Sym2.map.injective Subtype.val_injective heq))
        exact le_trans this (by convert (SimpleGraph.edgeFinset_card (G := completeOn s)).symm.le)
      _ = Fintype.card (SimpleGraph (Fin n)) := by linarith [hdecomp]
  calc (Finset.univ.filter (fun G : SimpleGraph (Fin n) => ¬G.CliqueFree k)).card *
    2 ^ k.choose 2
    ≤ (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      (Finset.univ.filter (fun G : SimpleGraph (Fin n) => completeOn s ≤ G)).card) *
      2 ^ k.choose 2 := Nat.mul_le_mul_right _ hunion
    _ = ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ((Finset.univ.filter (fun G : SimpleGraph (Fin n) => completeOn s ≤ G)).card *
        2 ^ k.choose 2) := by rw [Finset.sum_mul]
    _ ≤ ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      Fintype.card (SimpleGraph (Fin n)) :=
      Finset.sum_le_sum hIci_bound
    _ = ((Finset.univ : Finset (Fin n)).powersetCard k).card *
      Fintype.card (SimpleGraph (Fin n)) := by rw [Finset.sum_const, smul_eq_mul]
    _ = n.choose k * Fintype.card (SimpleGraph (Fin n)) := by
      congr 1; rw [Finset.card_powersetCard]; simp [Fintype.card_fin]

end CliqueNumber

namespace CliqueNumber

/--
[clique_number_first_moment_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/CliqueNumber.lean)
-/
@[path]
lemma clique_number_first_moment_bound
  {k : ℕ → ℕ}
-- given
  (hf : Tendsto (fun n => expectedKCliques n (k n)) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => probCliqueGe n (k n)) atTop (𝓝 0) :=
-- proof
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hf
    (fun n => probCliqueGe_nonneg n (k n)) (fun n => markov_bound n (k n))
/-- Second moment direction (Theorem 4.4.2): if the expected number of $k(n)$-cliques
  tends to infinity, then $G(n, 1/2)$ contains a $k(n)$-clique with probability tending
  to $1$. -/

end CliqueNumber

/--
[ba_sup_inf_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/CliqueNumber.lean)
-/
@[path]
private lemma ba_sup_inf_right_eq
  [BooleanAlgebra α]
  {a H K : α}
-- given
  (hH : H ≤ a)
  (hK : K ≤ aᶜ) :
-- imply
  (H ⊔ K) ⊓ a = H := by
-- proof
  apply CliqueNumber.ba_sup_inf_right hH hK

/--
[ba_sup_inf_compl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/CliqueNumber.lean)
-/
@[path]
private lemma ba_sup_inf_compl_eq
  [BooleanAlgebra α]
  {a H K : α}
-- given
  (hH : H ≤ a)
  (hK : K ≤ aᶜ) :
-- imply
  (H ⊔ K) ⊓ aᶜ = K := by
-- proof
  apply CliqueNumber.ba_sup_inf_compl hH hK


-- created on 2026-10-23
