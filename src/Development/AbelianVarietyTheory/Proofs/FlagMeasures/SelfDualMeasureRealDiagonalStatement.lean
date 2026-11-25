module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureRealDiagonal
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.self_dual_measure_real_diagonal : ∀ (κ : Type) [Fintype κ] (d : κ → ℝ), (∀ k, d k ≠ 0) → ∀ μ : Measure (κ → ℝ), SelfDual μ (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((∑ k, d k * (x k * y k) : ℝ) : ℂ))) → μ = ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ)) := by
  first | exact @GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag | exact GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag | (intros; apply GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag <;> assumption)
