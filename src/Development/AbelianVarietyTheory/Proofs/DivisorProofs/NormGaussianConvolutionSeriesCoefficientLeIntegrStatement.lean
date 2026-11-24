module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowForm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaussianConvolutionSeriesCoefficientLeIntegr
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.norm_gaussianConvolutionSeriesCoefficient_le_integral : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 ≤ b → 0 ≤ c → ∀ (h : SchwartzMap E ℂ) (j : ℕ),
    ‖GlobalTheory.ConvSeries.coef b c (⇑h) j‖ ≤ ∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j := by
  first | exact @GlobalTheory.ConvSeries.norm_coef_le_integral | exact GlobalTheory.ConvSeries.norm_coef_le_integral | (intros; apply GlobalTheory.ConvSeries.norm_coef_le_integral <;> assumption)
