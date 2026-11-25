module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Supplements.MathlibImports.AnalysisAndTactics
import Mathlib.Tactic.TypeStar
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets

open Formalism.BasicNotions Formalism.MainNotions

def jetAt {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) : ℂ_[p] :=
  (α.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff α F

def JetsIntegral {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ α, ‖jetAt F α‖ ≤ 1

end GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets
