module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexCoordinatesMeasurePreserving
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.complex_coordinates_measure_preserving : ∀ (ι : Type) [Fintype ι] (n : ℕ), ∃ T : (ι → Fin n → ℂ) ≃ₜ+ (ι × Fin n × Bool → ℝ), MeasurePreserving T volume volume ∧ ∀ y v i, T y (v, i, true) = (y v i).re ∧ T y (v, i, false) = (y v i).im := by
  first | exact @GlobalTheory.ReImVolume.exists_reIm_measurePreserving | exact GlobalTheory.ReImVolume.exists_reIm_measurePreserving | (intros; apply GlobalTheory.ReImVolume.exists_reIm_measurePreserving <;> assumption)
