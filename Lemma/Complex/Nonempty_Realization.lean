import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.LieGroups.code.SL2Classification
open Complex SL2SimpleModule
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.style.haveILetI false
set_option linter.deprecated false


/--
[SL2IrredGKModule.Realization.exists'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Classification.lean)
-/
@[path]
private lemma SL2IrredGKModule.Realization.exists'
  {μ : SL2IrredGKModule}
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  {K : Type*}
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)} :
-- imply
  Nonempty (SL2IrredGKModule.Realization μ 𝔤 K 𝔨 Ad) :=
-- proof
  sl2IrredGKModule_realization_exists μ 𝔤 K 𝔨 Ad

/--
[GKModule.isIrreducibleGKModule_of_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Classification.lean)
-/
@[path]
private lemma GKModule.isIrreducibleGKModule_of_iso
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  [AddCommGroup W]
  [Module ℂ W]
  [LieRingModule 𝔤 W]
  [LieModule ℂ 𝔤 W]
  {M : GKModule 𝔤 K 𝔨 Ad V}
  {N : GKModule 𝔤 K 𝔨 Ad W}
-- given
  (hiso : M.IsIsomorphicGK N)
  (hirr : M.IsIrreducibleGKModule) :
-- imply
  N.IsIrreducibleGKModule := by
-- proof
  obtain ⟨φ, hφ⟩ := hiso
  let e := LinearEquiv.ofBijective φ.toLinearMap hφ
  intro U hU
  let U' := U.comap e.toLinearMap
  have hU' : M.IsSubmodule U' := by
    constructor
    ·
      intro X v (hv : e.toLinearMap v ∈ U)
      show e.toLinearMap (Bracket.bracket X v) ∈ U
      rw [show e.toLinearMap (Bracket.bracket X v) = φ.toLinearMap (Bracket.bracket X v) from rfl,
        φ.lie_comm]
      exact hU.lie_invariant X (e.toLinearMap v) hv
    ·
      intro k v (hv : e.toLinearMap v ∈ U)
      show e.toLinearMap (M.σ k v) ∈ U
      rw [show e.toLinearMap (M.σ k v) = φ.toLinearMap (M.σ k v) from rfl, φ.group_comm]
      exact hU.group_invariant k (e.toLinearMap v) hv
  obtain h | h := hirr U' hU'
  ·
    left
    rw [Submodule.eq_bot_iff] at h ⊢
    intro w hw
    have hew : e.symm w ∈ U' := by
      change e.toLinearMap (e.symm w) ∈ U
      simp [hw]
    have h0 := h (e.symm w) hew
    have : w = 0 := by
      have : e (e.symm w) = e 0 := by rw [h0]
      simp at this
      exact this
    exact this
  ·
    right
    rw [Submodule.eq_top_iff'] at h ⊢
    intro w
    have : e.symm w ∈ U' := h (e.symm w)
    show w ∈ U
    have : e.toLinearMap (e.symm w) ∈ U := this
    rwa [show e.toLinearMap (e.symm w) = w from e.apply_symm_apply w] at this

/--
[sl2_classification_existence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Classification.lean)
-/
@[path]
private lemma sl2_classification_existence
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {M : GKModule 𝔤 K 𝔨 Ad V}
  {M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V}
-- given
  (hirr : M.IsIrreducibleGKModule)
  (hadm : M.IsAdmissible) :
-- imply
  ∃ (μ : SL2IrredGKModule) (R : SL2IrredGKModule.Realization.{_, _, 0} μ 𝔤 K 𝔨 Ad),
    M.IsIsomorphicGK R.gkmod :=
-- proof
  sl2_gk_classification 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm

/--
[sl2_principalSeriesEven_neg_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Classification.lean)
-/
@[path]
private lemma sl2_principalSeriesEven_neg_iso
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  {s : ℂ}
  {R₁ : SL2IrredGKModule.Realization (.principalSeries s 0) 𝔤 K 𝔨 Ad}
  {R₂ : SL2IrredGKModule.Realization (.principalSeries (-s) 0) 𝔤 K 𝔨 Ad}
-- given
  (_ : ¬ IsOddInteger s)
  (_ : ¬ IsOddInteger (-s)) :
-- imply
  R₁.gkmod.IsIsomorphicGK R₂.gkmod :=
-- proof
  principalSeries_neg_iso s 0 R₁ R₂

/--
[sl2_principalSeriesOdd_neg_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Classification.lean)
-/
@[path]
private lemma sl2_principalSeriesOdd_neg_iso
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  {s : ℂ}
  {R₁ : SL2IrredGKModule.Realization (.principalSeries s 1) 𝔤 K 𝔨 Ad}
  {R₂ : SL2IrredGKModule.Realization (.principalSeries (-s) 1) 𝔤 K 𝔨 Ad}
-- given
  (_ : ¬ IsEvenInteger s)
  (_ : ¬ IsEvenInteger (-s)) :
-- imply
  R₁.gkmod.IsIsomorphicGK R₂.gkmod :=
-- proof
  principalSeries_neg_iso s 1 R₁ R₂

/--
[sl2_classification_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Classification.lean)
-/
@[path]
private lemma sl2_classification_uniqueness
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  {μ ν : SL2IrredGKModule}
-- given
  (Rμ : SL2IrredGKModule.Realization μ 𝔤 K 𝔨 Ad)
  (Rν : SL2IrredGKModule.Realization ν 𝔤 K 𝔨 Ad)
  (hiso : Rμ.gkmod.IsIsomorphicGK Rν.gkmod) :
-- imply
  μ = ν ∨ ∃ s ε, μ = .principalSeries s ε ∧ ν = .principalSeries (-s) ε :=
-- proof
  sl2_iso_implies_label_match μ ν Rμ Rν hiso


-- created on 2026-10-23
-- updated on 2026-10-26
