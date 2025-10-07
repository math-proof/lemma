import Lemma.Bool.Imp.is.Or_Not
import Lemma.Logic.NotOr.is.AndNotS
import Lemma.Logic.NotAnd.is.OrNotS
import Lemma.Logic.IffNotNot
import Lemma.Logic.AndOr.is.OrAndS
import Lemma.Logic.And_Or.is.OrAndS
import Lemma.Logic.AndAnd.is.And_And
import Lemma.Logic.Or_Not.is.NotAndNot
open Logic Bool


@[main]
private lemma main
-- given
  (h₀ : p₀ → q₀)
  (h₁ : p₁ → q₁) :
-- imply
  p₀ ∨ p₁ → q₀ ∨ q₁ := by
-- proof
  apply Imp.of.Or_Not
  rw [NotOr.is.AndNotS]
  by_contra h
  rw [NotOr.is.AndNotS] at h
  rw [NotAnd.is.OrNotS] at h
  rw [IffNotNot, IffNotNot] at h
  rw [NotOr.is.AndNotS] at h
  have h₀ := Or_Not.of.Imp h₀
  have := And.intro h₀ h
  rw [And_And.is.AndAnd] at this
  rw [And_And.is.AndAnd] at this
  rw [AndOr.is.OrAndS] at this
  simp at this
  have := OrAndS.of.And_Or this.1 this.2
  rw [And.comm (b := p₀)] at this
  rw [And_And.is.AndAnd] at this
  rw [And_And.is.AndAnd] at this
  simp at this
  rw [AndAnd.is.And_And] at this
  let ⟨_, h_And⟩ := this
  have := Or_Not.of.Imp h₁
  have := And.intro h_And this
  rw [Or_Not.is.NotAndNot] at this
  let ⟨h_And, h_Not⟩ := this
  contradiction


-- created on 2025-04-11
-- updated on 2025-04-12
