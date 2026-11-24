module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanFundamentalDomainOfLe
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.mean_fundamentalDomain_eq_one_of_le : ∀ (g : ℕ) (Λ Λ₁ : AddSubgroup (Fin g → ℂ)) (Fd D₁ : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → ℝ), Countable Λ₁ → Λ ≤ Λ₁ → IsAddFundamentalDomain Λ Fd volume → IsAddFundamentalDomain Λ₁ D₁ volume → volume Fd ≠ ⊤ → (∀ a ∈ Λ₁, ∀ z, f (z + a) = f z) → (∫ z in D₁, f z) / (volume D₁).toReal = 1 → IntegrableOn f Fd volume ∧ (∫ z in Fd, f z) / (volume Fd).toReal = 1 := by
  first | exact @GlobalTheory.mean_fundamentalDomain_of_le | exact GlobalTheory.mean_fundamentalDomain_of_le | (intros; apply GlobalTheory.mean_fundamentalDomain_of_le <;> assumption)
