import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.CoxeterComplexFoldings
open ChamberComplex Garrett.ExchangeDeletion AptIsCoxeterProof CoxeterComplexData
open scoped Classical
open Garrett.ExchangeDeletion
open AptIsCoxeterProof


/--
[CoxeterSystem.simple_inv_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
@[path]
private lemma main
  [DecidableEq V]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M M.Group}
  {i : B} :
-- imply
  (cs.simple i)⁻¹ = cs.simple i :=
-- proof
  mul_left_cancel (by rw [mul_inv_cancel, cs.simple_mul_simple_self])


/--
[positive_or_negative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma positive_or_negative
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {s : data.B}
  {w : data.M.Group} :
-- imply
  data.inPositiveHalf s w ∨ data.inNegativeHalf s w := by
-- proof
  unfold inPositiveHalf inNegativeHalf
  obtain h | h <;> [left; right] <;> exact h := data.cs.length_simple_mul w s



/--
[one_in_positive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma one_in_positive
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {s : data.B} :
-- imply
  data.inPositiveHalf s 1 := by
-- proof
  unfold inPositiveHalf; simp [CoxeterSystem.length_one, CoxeterSystem.length_simple]



/--
[simple_in_negative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma simple_in_negative
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {s : data.B} :
-- imply
  data.inNegativeHalf s (data.cs.simple s) := by
-- proof
  unfold inNegativeHalf
  rw [CoxeterSystem.simple_mul_simple_self, CoxeterSystem.length_one,
    CoxeterSystem.length_simple]



variable [DecidableEq V]
variable (data : CoxeterComplexData V)
/--
[chamberMapF₀_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma chamberMapF₀_pos {s : data.B} {w : data.M.Group}
  (hw : data.inPositiveHalf s w) : data.chamberMapF₀ s w = w := by
  unfold chamberMapF₀ inPositiveHalf at *; rw [if_pos hw]



variable [DecidableEq V]
variable (data : CoxeterComplexData V)
/--
[chamberMapF₀_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma chamberMapF₀_neg {s : data.B} {w : data.M.Group}
  (hw : data.inNegativeHalf s w) : data.chamberMapF₀ s w = data.cs.simple s * w := by
  unfold chamberMapF₀ inNegativeHalf at *
  rw [if_neg (by omega)]



/--
[neg_of_mul_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma neg_of_mul_pos
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {s : data.B}
  {w : data.M.Group}
-- given
  (hw : data.inPositiveHalf s w) :
-- imply
  data.inNegativeHalf s (data.cs.simple s * w) := by
-- proof
  unfold inPositiveHalf inNegativeHalf at *
  rw [← mul_assoc, CoxeterSystem.simple_mul_simple_self, one_mul]; omega



/--
[pos_of_mul_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma pos_of_mul_neg
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {s : data.B}
  {w : data.M.Group}
-- given
  (hw : data.inNegativeHalf s w) :
-- imply
  data.inPositiveHalf s (data.cs.simple s * w) := by
-- proof
  unfold inPositiveHalf inNegativeHalf at *
  rw [← mul_assoc, CoxeterSystem.simple_mul_simple_self, one_mul]; omega



variable [DecidableEq V]
variable (data : CoxeterComplexData V)
/--
[chamberMapF₀_idempotent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma chamberMapF₀_idempotent (s : data.B) (w : data.M.Group) :
  data.chamberMapF₀ s (data.chamberMapF₀ s w) = data.chamberMapF₀ s w := by
  obtain hp | hn := data.positive_or_negative s w
  · rw [data.chamberMapF₀_pos hp, data.chamberMapF₀_pos hp]
  · rw [data.chamberMapF₀_neg hn, data.chamberMapF₀_pos (data.pos_of_mul_neg hn)]



variable [DecidableEq V]
variable (data : CoxeterComplexData V)
/--
[chamberMapF₀_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma chamberMapF₀_one (s : data.B) : data.chamberMapF₀ s 1 = 1 :=
  data.chamberMapF₀_pos (data.one_in_positive s)



variable [DecidableEq V]
variable (data : CoxeterComplexData V)
/--
[chamberMapF₀_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma chamberMapF₀_simple (s : data.B) :
  data.chamberMapF₀ s (data.cs.simple s) = 1 := by
  rw [data.chamberMapF₀_neg (data.simple_in_negative s),
    CoxeterSystem.simple_mul_simple_self]



variable [DecidableEq V]
variable (data : CoxeterComplexData V)
/--
[chamberMapF₀_two_to_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
/--
itself, namely $sw$ — the map is exactly two-to-one onto the positive half. -/
-/
private lemma chamberMapF₀_two_to_one (s : data.B) (w : data.M.Group)
  (hw : data.chamberMapF₀ s w = w) :
  ∃! w', w' ≠ w ∧ data.chamberMapF₀ s w' = w := by
  have hp : data.inPositiveHalf s w := by
    obtain hp | hn := data.positive_or_negative s w
    · exact hp
    · rw [data.chamberMapF₀_neg hn] at hw
      exfalso; unfold inNegativeHalf at hn
      rw [hw] at hn; omega
  refine ⟨data.cs.simple s * w, ⟨?_, ?_⟩, ?_⟩
  · intro h; unfold inPositiveHalf at hp; rw [h] at hp; omega
  · rw [data.chamberMapF₀_neg (data.neg_of_mul_pos hp),
    ← mul_assoc, CoxeterSystem.simple_mul_simple_self, one_mul]
  · intro w' ⟨hw'ne, hw'eq⟩
    obtain hp' | hn' := data.positive_or_negative s w'
    · rw [data.chamberMapF₀_pos hp'] at hw'eq; exact absurd hw'eq.symm (Ne.symm hw'ne)
    · rw [data.chamberMapF₀_neg hn'] at hw'eq
      calc w' = data.cs.simple s * (data.cs.simple s * w') := by
        rw [← mul_assoc, CoxeterSystem.simple_mul_simple_self, one_mul]
        _ = data.cs.simple s * w := by rw [hw'eq]



/--
[no_pos_neg_down](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma no_pos_neg_down
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {s : data.B}
  {w : data.M.Group}
  {t : data.B}
-- given
  (hp : data.inPositiveHalf s w)
  (hn : data.inNegativeHalf s (w * data.cs.simple t))
  (hdown : data.cs.length (w * data.cs.simple t) + 1 = data.cs.length w) :
-- imply
  False := by
-- proof
  unfold inPositiveHalf at hp; unfold inNegativeHalf at hn
  have hassoc : data.cs.simple s * (w * data.cs.simple t) =
    data.cs.simple s * w * data.cs.simple t := by group
  rw [hassoc] at hn
  obtain h | h := data.cs.length_mul_simple (data.cs.simple s * w * data.cs.simple t) t
  · rw [mul_assoc, CoxeterSystem.simple_mul_simple_self, mul_one] at h; omega
  · rw [mul_assoc, CoxeterSystem.simple_mul_simple_self, mul_one] at h; omega



/--
[no_neg_pos_up](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma no_neg_pos_up
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {s : data.B}
  {w : data.M.Group}
  {t : data.B}
-- given
  (hn : data.inNegativeHalf s w)
  (hp : data.inPositiveHalf s (w * data.cs.simple t))
  (hup : data.cs.length (w * data.cs.simple t) = data.cs.length w + 1) :
-- imply
  False := by
-- proof
  unfold inNegativeHalf at hn; unfold inPositiveHalf at hp
  have hassoc : data.cs.simple s * (w * data.cs.simple t) =
    data.cs.simple s * w * data.cs.simple t := by group
  rw [hassoc] at hp
  obtain h | h := data.cs.length_mul_simple (data.cs.simple s * w) t
  · omega
  · omega



variable [DecidableEq V]
variable (data : CoxeterComplexData V)
/--
[chamberMapF₀_preserves_adj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
$f_0^s$ to chambers that are either equal or still adjacent — folds do not
tear adjacencies apart. -/
private lemma chamberMapF₀_preserves_adj (s : data.B) (w : data.M.Group) (t : data.B) :
  data.chamberOf (data.chamberMapF₀ s (w * data.cs.simple t)) =
    data.chamberOf (data.chamberMapF₀ s w) ∨
  data.cc.toSimplicialComplex.Adjacent
    (data.chamberOf (data.chamberMapF₀ s w))
    (data.chamberOf (data.chamberMapF₀ s (w * data.cs.simple t))) := by
  obtain hp_w | hn_w <;> := data.positive_or_negative s w
  obtain hp_wt | hn_wt <;> := data.positive_or_negative s (w * data.cs.simple t)
  obtain h_up | h_down := data.cs.length_mul_simple w t
  ·
    rw [data.chamberMapF₀_pos hp_w, data.chamberMapF₀_pos hp_wt]
    right; exact data.adj_of_mul_simple w t
  ·
    rw [data.chamberMapF₀_pos hp_w, data.chamberMapF₀_pos hp_wt]
    right; exact data.adj_of_mul_simple w t
  ·
    rw [data.chamberMapF₀_pos hp_w, data.chamberMapF₀_neg hn_wt]
    have hex := corollary_of_exchange data.cs data.exchange w s t hp_w h_up
    obtain h_long | h_eq := hex
    · unfold inNegativeHalf at hn_wt
      rw [show data.cs.simple s * (w * data.cs.simple t) =
        data.cs.simple s * w * data.cs.simple t from by group] at hn_wt
      omega
    · left; rw [show data.cs.simple s * (w * data.cs.simple t) =
      data.cs.simple s * w * data.cs.simple t from by group]
      exact congrArg data.chamberOf h_eq
  ·
    exact (data.no_pos_neg_down s w t hp_w hn_wt h_down).elim
  ·
    exact (data.no_neg_pos_up s w t hn_w hp_wt h_up).elim
  ·
    rw [data.chamberMapF₀_neg hn_w, data.chamberMapF₀_pos hp_wt]
    unfold inNegativeHalf at hn_w; unfold inPositiveHalf at hp_wt
    have hassoc_swt : data.cs.simple s * (w * data.cs.simple t) =
      data.cs.simple s * w * data.cs.simple t := by group
    rw [hassoc_swt] at hp_wt
    have h_ssw : data.cs.length (data.cs.simple s * (data.cs.simple s * w)) =
      data.cs.length (data.cs.simple s * w) + 1 := by
      rw [← mul_assoc, CoxeterSystem.simple_mul_simple_self, one_mul]; omega
    have h_swt_up : data.cs.length (data.cs.simple s * w * data.cs.simple t) =
      data.cs.length (data.cs.simple s * w) + 1 := by omega
    have hex := corollary_of_exchange data.cs data.exchange (data.cs.simple s * w) s t
      h_ssw h_swt_up
    obtain h_long | h_eq := hex
    · simp at h_long; omega
    · simp at h_eq
      left; exact congrArg data.chamberOf h_eq
  ·
    rw [data.chamberMapF₀_neg hn_w, data.chamberMapF₀_neg hn_wt]
    rw [show data.cs.simple s * (w * data.cs.simple t) =
      data.cs.simple s * w * data.cs.simple t from by group]
    right; exact data.adj_of_mul_simple (data.cs.simple s * w) t
  ·
    rw [data.chamberMapF₀_neg hn_w, data.chamberMapF₀_neg hn_wt]
    rw [show data.cs.simple s * (w * data.cs.simple t) =
      data.cs.simple s * w * data.cs.simple t from by group]
    right; exact data.adj_of_mul_simple (data.cs.simple s * w) t



/--
[left_mul_preserves_adj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma left_mul_preserves_adj
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {w a b : data.M.Group}
-- given
  (hadj : data.cc.toSimplicialComplex.Adjacent (data.chamberOf a) (data.chamberOf b)) :
-- imply
  data.cc.toSimplicialComplex.Adjacent (data.chamberOf (w * a)) (data.chamberOf (w * b)) := by
-- proof
  obtain ⟨i, hi⟩ := data.adj_implies_mul_simple a (data.chamberOf b) hadj
  have hab : b = a * data.cs.simple i := data.chamberOf_injective hi
  rw [hab, show w * (a * data.cs.simple i) = w * a * data.cs.simple i from by group]
  exact data.adj_of_mul_simple (w * a) i



variable [DecidableEq V]
variable (data : CoxeterComplexData V)
/--
[conjugatedF₀_fixes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma conjugatedF₀_fixes (w : data.M.Group) (s : data.B) :
  data.conjugatedF₀ w s w = w := by
  simp [conjugatedF₀, data.chamberMapF₀_one, mul_one]



variable [DecidableEq V]
variable (data : CoxeterComplexData V)
/--
[conjugatedF₀_folds](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma conjugatedF₀_folds (w : data.M.Group) (s : data.B) :
  data.conjugatedF₀ w s (w * data.cs.simple s) = w := by
  simp [conjugatedF₀, inv_mul_cancel_left, data.chamberMapF₀_simple, mul_one]



variable [DecidableEq V]
variable (data : CoxeterComplexData V)
/--
[conjugatedF₀_idempotent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma conjugatedF₀_idempotent (w : data.M.Group) (s : data.B) (u : data.M.Group) :
  data.conjugatedF₀ w s (data.conjugatedF₀ w s u) =
  data.conjugatedF₀ w s u := by
  simp [conjugatedF₀, data.chamberMapF₀_idempotent]



variable [DecidableEq V]
variable (data : CoxeterComplexData V)
/--
[conjugatedF₀_not_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma conjugatedF₀_not_id (w : data.M.Group) (s : data.B) :
  ∃ u, data.conjugatedF₀ w s u ≠ u := by
  use w * data.cs.simple s
  rw [data.conjugatedF₀_folds]
  intro h
  have h1 := data.cs.length_simple s
  have : data.cs.simple s = (1 : data.M.Group) := by
    have := data.chamberOf_injective (congrArg data.chamberOf h)
    rwa [left_eq_mul] at this
  rw [this, CoxeterSystem.length_one] at h1; omega



variable [DecidableEq V]
variable (data : CoxeterComplexData V)
/--
[conjugatedF₀_two_to_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
/--
itself, namely $wsw^{-1}u$. -/
-/
private lemma conjugatedF₀_two_to_one (w : data.M.Group) (s : data.B)
  (u : data.M.Group) (hu : data.conjugatedF₀ w s u = u) :
  ∃! u', u' ≠ u ∧ data.conjugatedF₀ w s u' = u := by
  have hv : data.chamberMapF₀ s (w⁻¹ * u) = w⁻¹ * u := by
    have h1 := hu; unfold conjugatedF₀ at h1
    have h2 : w⁻¹ * (w * data.chamberMapF₀ s (w⁻¹ * u)) = w⁻¹ * u :=
      congrArg (w⁻¹ * ·) h1
    rwa [inv_mul_cancel_left] at h2
  obtain ⟨v', ⟨hv'ne, hv'eq⟩, hv'uniq⟩ :=
    data.chamberMapF₀_two_to_one s (w⁻¹ * u) hv
  refine ⟨w * v', ⟨?_, ?_⟩, ?_⟩
  · intro h; apply hv'ne
    have : w⁻¹ * (w * v') = w⁻¹ * (w * (w⁻¹ * u)) := by rw [h, mul_inv_cancel_left]
    rwa [inv_mul_cancel_left, inv_mul_cancel_left] at this
  · unfold conjugatedF₀
    simp only [inv_mul_cancel_left]
    rw [hv'eq, mul_inv_cancel_left]
  · intro u' ⟨hu'ne, hu'eq⟩
    have hv'' : w⁻¹ * u' ≠ w⁻¹ * u := by
      intro h; apply hu'ne
      have : w * (w⁻¹ * u') = w * (w⁻¹ * u) := congrArg (w * ·) h
      rwa [mul_inv_cancel_left, mul_inv_cancel_left] at this
    have hv''eq : data.chamberMapF₀ s (w⁻¹ * u') = w⁻¹ * u := by
      unfold conjugatedF₀ at hu'eq
      have h2 : w⁻¹ * (w * data.chamberMapF₀ s (w⁻¹ * u')) = w⁻¹ * u :=
        congrArg (w⁻¹ * ·) hu'eq
      rwa [inv_mul_cancel_left] at h2
    have := hv'uniq (w⁻¹ * u') ⟨hv'', hv''eq⟩
    calc u' = w * (w⁻¹ * u') := by rw [mul_inv_cancel_left]
      _ = w * v' := by rw [this]



variable [DecidableEq V]
variable (data : CoxeterComplexData V)
/--
[conjugatedF₀_preserves_adj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
/--
chambers $C_u, C_{us_t}$ go to chambers that are equal or still adjacent. -/
-/
private lemma conjugatedF₀_preserves_adj (w : data.M.Group) (s : data.B)
  (u : data.M.Group) (t : data.B) :
  data.chamberOf (data.conjugatedF₀ w s (u * data.cs.simple t)) =
    data.chamberOf (data.conjugatedF₀ w s u) ∨
  data.cc.toSimplicialComplex.Adjacent
    (data.chamberOf (data.conjugatedF₀ w s u))
    (data.chamberOf (data.conjugatedF₀ w s (u * data.cs.simple t))) := by
  unfold conjugatedF₀
  rw [show w⁻¹ * (u * data.cs.simple t) = w⁻¹ * u * data.cs.simple t from by group]
  obtain heq | hadj := data.chamberMapF₀_preserves_adj s (w⁻¹ * u) t
  · left
    have := data.chamberOf_injective heq
    show data.chamberOf (w * data.chamberMapF₀ s (w⁻¹ * u * data.cs.simple t)) =
      data.chamberOf (w * data.chamberMapF₀ s (w⁻¹ * u))
    rw [this]
  · right; exact data.left_mul_preserves_adj w _ _ hadj


/--
[chamberMapF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma chamberMapF_eq
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {s : data.B}
  {w : data.M.Group}
-- given
  (hw : data.inPositiveHalf s w) :
-- imply
  data.chamberMapF₀ s w = w := by
-- proof
  apply CoxeterComplexData.chamberMapF data hw

/--
[chamberMapF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma chamberMapF_eq_2
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {s : data.B}
  {w : data.M.Group}
-- given
  (hw : data.inNegativeHalf s w) :
-- imply
  data.chamberMapF₀ s w = data.cs.simple s * w := by
-- proof
  apply CoxeterComplexData.chamberMapF data hw

/--
[chamberMapF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma chamberMapF_eq_3
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {s : data.B}
  {w : data.M.Group} :
-- imply
  data.chamberMapF₀ s (data.chamberMapF₀ s w) = data.chamberMapF₀ s w := by
-- proof
  apply CoxeterComplexData.chamberMapF data s w

/--
[chamberMapF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma chamberMapF_eq_4
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {s : data.B} :
-- imply
  data.chamberMapF₀ s 1 = 1 := by
-- proof
  apply CoxeterComplexData.chamberMapF data s

/--
[chamberMapF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma chamberMapF_eq_5
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {s : data.B} :
-- imply
  data.chamberMapF₀ s (data.cs.simple s) = 1 := by
-- proof
  apply CoxeterComplexData.chamberMapF data s

/--
[chamberMapF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma chamberMapF_eq_6
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {s : data.B}
  {w : data.M.Group}
-- given
  (hw : data.chamberMapF₀ s w = w) :
-- imply
  ∃! w', w' ≠ w ∧ data.chamberMapF₀ s w' = w := by
-- proof
  apply CoxeterComplexData.chamberMapF data s w hw

/--
[chamberMapF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma chamberMapF_eq_7
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {s : data.B}
  {w : data.M.Group}
  {t : data.B} :
-- imply
  data.chamberOf (data.chamberMapF₀ s (w * data.cs.simple t)) = data.chamberOf (data.chamberMapF₀ s w) ∨ data.cc.toSimplicialComplex.Adjacent (data.chamberOf (data.chamberMapF₀ s w)) (data.chamberOf (data.chamberMapF₀ s (w * data.cs.simple t))) := by
-- proof
  apply CoxeterComplexData.chamberMapF data s w t

/--
[conjugatedF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma conjugatedF_eq
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {w : data.M.Group}
  {s : data.B} :
-- imply
  data.conjugatedF₀ w s w = w := by
-- proof
  apply CoxeterComplexData.conjugatedF data w s

/--
[conjugatedF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma conjugatedF_eq_2
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {w : data.M.Group}
  {s : data.B} :
-- imply
  data.conjugatedF₀ w s (w * data.cs.simple s) = w := by
-- proof
  apply CoxeterComplexData.conjugatedF data w s

/--
[conjugatedF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma conjugatedF_eq_3
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {w : data.M.Group}
  {s : data.B}
  {u : data.M.Group} :
-- imply
  data.conjugatedF₀ w s (data.conjugatedF₀ w s u) = data.conjugatedF₀ w s u := by
-- proof
  apply CoxeterComplexData.conjugatedF data w s u

/--
[conjugatedF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma conjugatedF_eq_4
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {w : data.M.Group}
  {s : data.B} :
-- imply
  ∃ u, data.conjugatedF₀ w s u ≠ u := by
-- proof
  apply CoxeterComplexData.conjugatedF data w s

/--
[conjugatedF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma conjugatedF_eq_5
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {w : data.M.Group}
  {s : data.B}
  {u : data.M.Group}
-- given
  (hu : data.conjugatedF₀ w s u = u) :
-- imply
  ∃! u', u' ≠ u ∧ data.conjugatedF₀ w s u' = u := by
-- proof
  apply CoxeterComplexData.conjugatedF data w s u hu

/--
[conjugatedF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean)
-/
private lemma conjugatedF_eq_6
  [DecidableEq V]
  {data : CoxeterComplexData V}
  {w : data.M.Group}
  {s : data.B}
  {u : data.M.Group}
  {t : data.B} :
-- imply
  data.chamberOf (data.conjugatedF₀ w s (u * data.cs.simple t)) = data.chamberOf (data.conjugatedF₀ w s u) ∨ data.cc.toSimplicialComplex.Adjacent (data.chamberOf (data.conjugatedF₀ w s u)) (data.chamberOf (data.conjugatedF₀ w s (u * data.cs.simple t))) := by
-- proof
  apply CoxeterComplexData.conjugatedF data w s u t


-- created on 2026-10-23
-- updated on 2026-10-26
