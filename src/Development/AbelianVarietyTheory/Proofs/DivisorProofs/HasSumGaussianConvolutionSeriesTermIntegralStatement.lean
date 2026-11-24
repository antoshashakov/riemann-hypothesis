module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowForm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumGaussianConvolutionSeriesTermIntegral
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.hasSum_gaussianConvolutionSeriesTerm_integral : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 < b → 0 < c → ∀ (h : SchwartzMap E ℂ) (y : E),
    HasSum (fun k => GlobalTheory.ConvSeries.term b c h k y)
      (∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) := by
  first | exact @GlobalTheory.ConvSeries.hasSum_term_integral | exact GlobalTheory.ConvSeries.hasSum_term_integral | (intros; apply GlobalTheory.ConvSeries.hasSum_term_integral <;> assumption)
