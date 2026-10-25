/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.CircuitLowerBound.Part6
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FK.FinitePatternEnergy
open MeasureTheory Finset


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


variable (C : SimpleGraph V) [DecidableRel C.Adj]


variable {C}


omit [Fintype V] in
@[simp] theorem setPattern_of_mem {I : Finset (Sym2 V)} (eta : ConfigSpace ↥I)
    {e : Sym2 V} (he : e ∈ I) (psi : ConfigSpace (Sym2 V)) :
    setPattern I eta psi e = eta ⟨e, he⟩ := by
  simp [setPattern, he]

omit [Fintype V] in
theorem setPattern_of_not_mem {I : Finset (Sym2 V)} (eta : ConfigSpace ↥I)
    {e : Sym2 V} (he : e ∉ I) (psi : ConfigSpace (Sym2 V)) :
    setPattern I eta psi e = psi e := by
  simp [setPattern, he]

omit [Fintype V] in
theorem setPattern_empty (eta : ConfigSpace ↥(∅ : Finset (Sym2 V)))
    (psi : ConfigSpace (Sym2 V)) : setPattern ∅ eta psi = psi := by
  funext e
  simp [setPattern]

omit [Fintype V] in
theorem setPattern_setClosed {I : Finset (Sym2 V)} (eta : ConfigSpace ↥I)
    {e : Sym2 V} (he : e ∉ I) (psi : ConfigSpace (Sym2 V)) :
    setPattern I eta (setClosed e psi) = setClosed e (setPattern I eta psi) := by
  funext x
  by_cases hxI : x ∈ I
  · have hxe : x ≠ e := fun h => he (h ▸ hxI)
    rw [setPattern_of_mem eta hxI, setClosed_of_ne hxe,
      setPattern_of_mem eta hxI]
  · by_cases hxe : x = e
    · subst x
      simp [setPattern, he]
    · rw [setPattern_of_not_mem eta hxI, setClosed_of_ne hxe,
        setClosed_of_ne hxe, setPattern_of_not_mem eta hxI]

omit [Fintype V] in
theorem setPattern_setOpen {I : Finset (Sym2 V)} (eta : ConfigSpace ↥I)
    {e : Sym2 V} (he : e ∉ I) (psi : ConfigSpace (Sym2 V)) :
    setPattern I eta (setOpen e psi) = setOpen e (setPattern I eta psi) := by
  funext x
  by_cases hxI : x ∈ I
  · have hxe : x ≠ e := fun h => he (h ▸ hxI)
    rw [setPattern_of_mem eta hxI, setOpen_of_ne hxe,
      setPattern_of_mem eta hxI]
  · by_cases hxe : x = e
    · subst x
      simp [setPattern, he]
    · rw [setPattern_of_not_mem eta hxI, setOpen_of_ne hxe,
        setOpen_of_ne hxe, setPattern_of_not_mem eta hxI]


variable (C : SimpleGraph V) [DecidableRel C.Adj]


theorem inducedBcZ_insert (p q : ℝ) {e : Sym2 V} {I : Finset (Sym2 V)}
    (he : e ∉ I) (psi : ConfigSpace (Sym2 V)) :
    inducedBcZ G C p q (insert e I) psi =
      inducedBcZ G C p q I (setClosed e psi) +
        inducedBcZ G C p q I (setOpen e psi) := by
  classical
  unfold inducedBcZ condFibre AgreesOff
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun sigma => sigma e = false)]
  congr 1
  · apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext sigma
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hfree, h0⟩
      intro e' he'
      by_cases hee : e' = e
      · subst e'
        rw [h0, setClosed_self]
      · rw [setClosed_of_ne hee]
        exact hfree e' (by simp [Finset.mem_insert, hee, he'])
    · intro hfree
      refine ⟨fun e' he' => ?_, ?_⟩
      · have hne : e' ≠ e := fun h => he' (h ▸ Finset.mem_insert_self e I)
        have h := hfree e' (fun hc => he' (Finset.mem_insert_of_mem hc))
        rwa [setClosed_of_ne hne] at h
      · have h := hfree e he
        rwa [setClosed_self] at h
  · apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext sigma
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_false]
    constructor
    · rintro ⟨hfree, h1⟩
      intro e' he'
      by_cases hee : e' = e
      · subst e'
        rw [h1, setOpen_self]
      · rw [setOpen_of_ne hee]
        exact hfree e' (by simp [Finset.mem_insert, hee, he'])
    · intro hfree
      refine ⟨fun e' he' => ?_, ?_⟩
      · have hne : e' ≠ e := fun h => he' (h ▸ Finset.mem_insert_self e I)
        have h := hfree e' (fun hc => he' (Finset.mem_insert_of_mem hc))
        rwa [setOpen_of_ne hne] at h
      · have h := hfree e he
        rwa [setOpen_self] at h


theorem inducedBcZ_empty (p q : ℝ) (psi : ConfigSpace (Sym2 V)) :
    inducedBcZ G C p q ∅ psi = bcWeight G C p q psi := by
  classical
  unfold inducedBcZ condFibre
  have hf : Finset.univ.filter (AgreesOff ∅ psi) = {psi} := by
    ext sigma
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      funext e
      exact h e (Finset.notMem_empty e)
    · intro h
      subst sigma
      exact fun _ _ => rfl
  rw [hf]
  simp


theorem cFE_pow_mul_inducedBcZ_le_setPattern
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I) (psi : ConfigSpace (Sym2 V)) :
    cFE p q ^ I.card * inducedBcZ G C p q I psi ≤
      bcWeight G C p q (setPattern I eta psi) := by
  classical
  induction I using Finset.induction generalizing psi with
  | empty =>
      rw [Finset.card_empty, pow_zero, one_mul, inducedBcZ_empty]
      rw [setPattern_empty]
  | @insert e I he ih =>
      let etaI : ConfigSpace ↥I := fun x => eta ⟨x, Finset.mem_insert_of_mem x.2⟩
      let rho := setPattern I etaI psi
      have hclosed : setPattern I etaI (setClosed e psi) = setClosed e rho := by
        simpa [rho] using setPattern_setClosed etaI he psi
      have hopen : setPattern I etaI (setOpen e psi) = setOpen e rho := by
        simpa [rho] using setPattern_setOpen etaI he psi
      have ihc := ih etaI (setClosed e psi)
      have iho := ih etaI (setOpen e psi)
      have htarget : setPattern (insert e I) eta psi =
          if eta ⟨e, Finset.mem_insert_self e I⟩ then setOpen e rho else setClosed e rho := by
        funext x
        by_cases heta : eta ⟨e, Finset.mem_insert_self e I⟩ = true
        · simp only [heta, if_true]
          by_cases hx : x = e
          · subst x
            simp [setPattern, rho, he, heta]
          · by_cases hxI : x ∈ I
            · rw [setOpen_of_ne hx]
              simp [setPattern, rho, hxI, hx, etaI]
            · rw [setOpen_of_ne hx]
              simp [setPattern, rho, hxI, hx, etaI]
        · have heta0 : eta ⟨e, Finset.mem_insert_self e I⟩ = false :=
            Bool.eq_false_of_not_eq_true heta
          simp only [heta0, Bool.false_eq_true, if_false]
          by_cases hx : x = e
          · subst x
            simp [setPattern, rho, he, heta0]
          · by_cases hxI : x ∈ I
            · rw [setClosed_of_ne hx]
              simp [setPattern, rho, hxI, hx, etaI]
            · rw [setClosed_of_ne hx]
              simp [setPattern, rho, hxI, hx, etaI]
      rw [Finset.card_insert_of_notMem he, pow_succ,
        inducedBcZ_insert G C p q he, htarget]
      have hc : 0 ≤ cFE p q := (cFE_pos hp hp1 hq).le
      have hsum : cFE p q ^ I.card *
            (inducedBcZ G C p q I (setClosed e psi) +
              inducedBcZ G C p q I (setOpen e psi)) ≤
          bcWeight G C p q (setClosed e rho) +
            bcWeight G C p q (setOpen e rho) := by
        calc
          cFE p q ^ I.card *
              (inducedBcZ G C p q I (setClosed e psi) +
                inducedBcZ G C p q I (setOpen e psi)) =
              cFE p q ^ I.card * inducedBcZ G C p q I (setClosed e psi) +
                cFE p q ^ I.card * inducedBcZ G C p q I (setOpen e psi) := by ring
          _ ≤ bcWeight G C p q (setPattern I etaI (setClosed e psi)) +
                bcWeight G C p q (setPattern I etaI (setOpen e psi)) :=
            add_le_add ihc iho
          _ = bcWeight G C p q (setClosed e rho) +
                bcWeight G C p q (setOpen e rho) := by rw [hclosed, hopen]
      calc
        cFE p q ^ I.card * cFE p q *
            (inducedBcZ G C p q I (setClosed e psi) +
              inducedBcZ G C p q I (setOpen e psi)) =
            cFE p q * (cFE p q ^ I.card *
              (inducedBcZ G C p q I (setClosed e psi) +
                inducedBcZ G C p q I (setOpen e psi))) := by ring
        _ ≤ cFE p q * (bcWeight G C p q (setClosed e rho) +
              bcWeight G C p q (setOpen e rho)) :=
          mul_le_mul_of_nonneg_left hsum hc
        _ = cFE p q * (bcWeight G C p q (setOpen e rho) +
              bcWeight G C p q (setClosed e rho)) := by ring
        _ ≤ (if eta ⟨e, Finset.mem_insert_self e I⟩ then
              bcWeight G C p q (setOpen e rho) else
              bcWeight G C p q (setClosed e rho)) := by
          split
          · exact bcWeight_setOpen_ge G C hp hp1 hq e rho
          · exact bcWeight_setClosed_ge G C hp hp1 hq e rho
        _ = bcWeight G C p q
            (if eta ⟨e, Finset.mem_insert_self e I⟩ then setOpen e rho
              else setClosed e rho) := by split <;> rfl

variable {C}


theorem cFE_pow_mul_agreeWeightSum_le_setPattern
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I) (psi : ConfigSpace (Sym2 V)) :
    cFE p q ^ I.card * agreeWeightSum G p q I psi ≤
      fkWeight G p q (setPattern I eta psi) := by
  classical
  induction I using Finset.induction generalizing psi with
  | empty =>
      rw [Finset.card_empty, pow_zero, one_mul, agreeWeightSum_empty]
      rw [setPattern_empty]
  | @insert e I he ih =>
      let etaI : ConfigSpace ↥I := fun x => eta ⟨x, Finset.mem_insert_of_mem x.2⟩
      let rho := setPattern I etaI psi
      have hclosed : setPattern I etaI (setClosed e psi) = setClosed e rho := by
        simpa [rho] using setPattern_setClosed etaI he psi
      have hopen : setPattern I etaI (setOpen e psi) = setOpen e rho := by
        simpa [rho] using setPattern_setOpen etaI he psi
      have ihc := ih etaI (setClosed e psi)
      have iho := ih etaI (setOpen e psi)
      have htarget : setPattern (insert e I) eta psi =
          if eta ⟨e, Finset.mem_insert_self e I⟩ then setOpen e rho else setClosed e rho := by
        funext x
        by_cases heta : eta ⟨e, Finset.mem_insert_self e I⟩ = true
        · simp only [heta, if_true]
          by_cases hx : x = e
          · subst x
            simp [setPattern, rho, he, heta]
          · by_cases hxI : x ∈ I
            · rw [setOpen_of_ne hx]
              simp [setPattern, rho, hxI, hx, etaI]
            · rw [setOpen_of_ne hx]
              simp [setPattern, rho, hxI, hx, etaI]
        · have heta0 : eta ⟨e, Finset.mem_insert_self e I⟩ = false := by
            exact Bool.eq_false_of_not_eq_true heta
          simp only [heta0, Bool.false_eq_true, if_false]
          by_cases hx : x = e
          · subst x
            simp [setPattern, rho, he, heta0]
          · by_cases hxI : x ∈ I
            · rw [setClosed_of_ne hx]
              simp [setPattern, rho, hxI, hx, etaI]
            · rw [setClosed_of_ne hx]
              simp [setPattern, rho, hxI, hx, etaI]
      rw [Finset.card_insert_of_notMem he, pow_succ,
        agreeWeightSum_insert G p q he, htarget]
      have hc : 0 ≤ cFE p q := (cFE_pos hp hp1 hq).le
      have hsum : cFE p q ^ I.card *
            (agreeWeightSum G p q I (setClosed e psi) +
              agreeWeightSum G p q I (setOpen e psi)) ≤
          fkWeight G p q (setClosed e rho) + fkWeight G p q (setOpen e rho) := by
        calc
          cFE p q ^ I.card *
              (agreeWeightSum G p q I (setClosed e psi) +
                agreeWeightSum G p q I (setOpen e psi)) =
              cFE p q ^ I.card * agreeWeightSum G p q I (setClosed e psi) +
                cFE p q ^ I.card * agreeWeightSum G p q I (setOpen e psi) := by ring
          _ ≤ fkWeight G p q (setPattern I etaI (setClosed e psi)) +
                fkWeight G p q (setPattern I etaI (setOpen e psi)) :=
            add_le_add ihc iho
          _ = fkWeight G p q (setClosed e rho) + fkWeight G p q (setOpen e rho) := by
            rw [hclosed, hopen]
      calc
        cFE p q ^ I.card * cFE p q *
            (agreeWeightSum G p q I (setClosed e psi) +
              agreeWeightSum G p q I (setOpen e psi)) =
            cFE p q * (cFE p q ^ I.card *
              (agreeWeightSum G p q I (setClosed e psi) +
                agreeWeightSum G p q I (setOpen e psi))) := by ring
        _ ≤ cFE p q *
            (fkWeight G p q (setClosed e rho) + fkWeight G p q (setOpen e rho)) :=
          mul_le_mul_of_nonneg_left hsum hc
        _ = cFE p q *
            (fkWeight G p q (setOpen e rho) + fkWeight G p q (setClosed e rho)) := by ring
        _ ≤ (if eta ⟨e, Finset.mem_insert_self e I⟩ then
              fkWeight G p q (setOpen e rho) else fkWeight G p q (setClosed e rho)) := by
          split
          · exact fkWeight_setOpen_ge G hp hp1 hq e rho
          · exact fkWeight_setClosed_ge G hp hp1 hq e rho
        _ = fkWeight G p q
            (if eta ⟨e, Finset.mem_insert_self e I⟩ then setOpen e rho else setClosed e rho) := by
          split <;> rfl


end FK
end StatMech
