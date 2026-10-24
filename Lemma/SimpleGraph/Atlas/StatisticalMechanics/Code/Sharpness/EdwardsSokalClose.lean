import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.EdwardsSokalClose
open StatMech StatMech.FK


/--
[esk_esWeight_spinsum_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EdwardsSokalClose.lean)
-/
@[path]
private lemma esk_esWeight_spinsum_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
  {g : (V → Fin q) → ℝ} :
-- imply
  (∑ σ : V → Fin q, esWeight G p σ ω * g σ) = edgeProduct G p ω * ∑ σ : V → Fin q, (if ConstOnOpen G ω σ then (1 : ℝ) else 0) * g σ := by
-- proof
  apply StatMech.FK.esk_esWeight_spinsum_factor G p ω g

/--
[esk_agree_spinsum_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EdwardsSokalClose.lean)
-/
@[path]
private lemma esk_agree_spinsum_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
  {x y : V} :
-- imply
  (∑ σ : V → Fin q, esWeight G p σ ω * (if σ x = σ y then (1:ℝ) else 0)) = edgeProduct G p ω * ((Finset.univ.filter (fun σ : V → Fin q => ConstOnOpen G ω σ ∧ σ x = σ y)).card : ℝ) := by
-- proof
  apply StatMech.FK.esk_agree_spinsum_card G p ω x y

/--
[esk_agree_spinsum_fkWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EdwardsSokalClose.lean)
-/
@[path]
private lemma esk_agree_spinsum_fkWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
  {x y : V}
-- given
  (hq : 0 < q) :
-- imply
  (∑ σ : V → Fin q, esWeight G p σ ω * (if σ x = σ y then (1:ℝ) else 0)) = if Connected G ω x y then fkWeight G p (q:ℝ) ω else fkWeight G p (q:ℝ) ω / (q:ℝ) := by
-- proof
  apply StatMech.FK.esk_agree_spinsum_fkWeight G hq p ω x y

/--
[esk_esAgreeProb_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EdwardsSokalClose.lean)
-/
@[path]
private lemma esk_esAgreeProb_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {x y : V}
-- given
  (hq : 0 < q)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  esAgreeProb G q p x y = connProb G p q x y + (1 - connProb G p q x y) / (q : ℝ) := by
-- proof
  apply StatMech.FK.esk_esAgreeProb_eq G hq p hp hp1 x y

/--
[esk_pottsCorr_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EdwardsSokalClose.lean)
-/
@[path]
private lemma esk_pottsCorr_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {x y : V}
-- given
  (hq : 0 < q)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  esAgreeProb G q p x y - 1 / (q : ℝ) = (((q : ℝ) - 1) / (q : ℝ)) * connProb G p q x y := by
-- proof
  apply StatMech.FK.esk_pottsCorr_eq G hq p hp hp1 x y

/--
[esk_esAgreeProb_eq_pottsAgreeProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EdwardsSokalClose.lean)
-/
@[path]
private lemma esk_esAgreeProb_eq_pottsAgreeProb_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {β J : ℝ}
  {x y : V} :
-- imply
  esAgreeProb G q (1 - Real.exp (-(β * J))) x y = esk_pottsAgreeProb G q β J x y := by
-- proof
  apply StatMech.FK.esk_esAgreeProb_eq_pottsAgreeProb G q β J x y

/--
[esk_edwardsSokal_correlation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EdwardsSokalClose.lean)
-/
@[path]
private lemma esk_edwardsSokal_correlation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  [NeZero q]
  {β J : ℝ}
  {x y : V}
-- given
  (hβJ : 0 < 1 - Real.exp (-(β * J)))
  (hβJ1 : 1 - Real.exp (-(β * J)) < 1) :
-- imply
  esk_pottsAgreeProb G q β J x y - 1 / (q : ℝ) = (((q : ℝ) - 1) / (q : ℝ)) * connProb G (1 - Real.exp (-(β * J))) q x y := by
-- proof
  apply StatMech.FK.esk_edwardsSokal_correlation G q β J hβJ hβJ1 x y

/--
[esk_pottsCorr_eq_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EdwardsSokalClose.lean)
-/
@[path]
private lemma esk_pottsCorr_eq_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj) (q : ℕ) (p : ℝ) (x y : V), (0 < q) ∧ (0 < p) ∧ (p < 1) ∧ (esAgreeProb G q p x y - 1 / (q : ℝ) = (((q : ℝ) - 1) / (q : ℝ)) * connProb G p q x y) := by
-- proof
  apply StatMech.FK.esk_pottsCorr_eq_nonvacuous G


-- created on 2026-10-23
