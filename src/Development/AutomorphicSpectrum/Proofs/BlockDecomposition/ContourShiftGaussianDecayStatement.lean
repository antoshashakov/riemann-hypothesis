module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContourShiftGaussianDecay
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

@[expose] public section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

theorem _root_.GlobalTheory.T.contour_shift_gaussian_decay : ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y] (f : ℂ → Y) (a b M : ℝ), a ≤ b → DifferentiableOn ℂ f {z : ℂ | z.re ∈ Set.Icc a b} → (∀ z : ℂ, z.re ∈ Set.Icc a b → ‖f z‖ ≤ M * Real.exp (-z.im ^ 2)) → ∫ y : ℝ, f ⟨a, y⟩ = ∫ y : ℝ, f ⟨b, y⟩ := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.ShiftLine.shift_vertical_line | exact GlobalTheory.CompanionTheory.TubeFourier.ShiftLine.shift_vertical_line | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.ShiftLine.shift_vertical_line <;> assumption)
