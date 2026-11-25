module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HarmonicAnnulusMaximumPrinciple
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

theorem _root_.GlobalTheory.T.harmonic_annulus_maximum_principle : ∀ (h : ℂ → ℝ) (a b : ℝ), 0 < a → a < b → ContinuousOn h {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} → (∀ z : ℂ, a < ‖z‖ → ‖z‖ < b → InnerProductSpace.HarmonicAt h z) → (∀ z : ℂ, (‖z‖ = a ∨ ‖z‖ = b) → h z ≤ 0) → ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → h z ≤ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.harmonic_annulus_le_zero | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.harmonic_annulus_le_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.harmonic_annulus_le_zero <;> assumption)
