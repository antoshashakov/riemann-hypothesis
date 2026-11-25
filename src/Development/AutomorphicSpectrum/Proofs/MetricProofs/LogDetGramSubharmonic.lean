module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XGramSize
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne

@[expose] public section

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem gram_det_log_size : ∀ (n k : ℕ) (G G₀ : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin k) ℂ) (m : ℝ), 1 ≤ m → G₀.PosDef → G.PosDef → ((m : ℂ) • G₀ - G).PosSemidef → ((m : ℂ) • G - G₀).PosSemidef → LinearIndependent ℂ Vᵀ → |Real.log (Vᴴ * G * V).det.re - Real.log (Vᴴ * G₀ * V).det.re| ≤ k * Real.log m :=
  PositivityTheory.Xgp.t_gram_size

end GlobalTheory.CompanionTheory.Ar.PB
