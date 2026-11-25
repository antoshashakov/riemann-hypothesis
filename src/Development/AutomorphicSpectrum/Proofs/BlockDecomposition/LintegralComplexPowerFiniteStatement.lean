module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralComplexPowerFinite
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC

@[expose] public section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem _root_.GlobalTheory.T.lintegral_complex_power_finite : ∀ (n : ℕ) (t : ℝ), (n : ℝ) < t →
    ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-t)) ≠ ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top <;> assumption)
