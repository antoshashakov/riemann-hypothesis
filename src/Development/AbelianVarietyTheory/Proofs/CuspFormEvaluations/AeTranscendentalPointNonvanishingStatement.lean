module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeTranscendentalPointNonvanishing
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.ae_transcendental_point_nonvanishing : ∀ (K : Type) [Field K] [Countable K] (σ : K →+* ℂ) (ι : Type) [Fintype ι], ∀ᵐ t : ι → ℂ, ∀ Q : MvPolynomial ι K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0 := by
  first | exact @GlobalTheory.ae_eval₂_ne_zero_of_countable | exact GlobalTheory.ae_eval₂_ne_zero_of_countable | (intros; apply GlobalTheory.ae_eval₂_ne_zero_of_countable <;> assumption)
