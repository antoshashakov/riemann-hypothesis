module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierProdSingleCoordinateFunctions
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

theorem _root_.GlobalTheory.T.fourier_prod_single_coordinate_functions : ∀ (I : Type) [Fintype I] (f : I → ℂ → ℂ), (∀ i, Integrable (f i)) → ∀ l : EuclideanSpace ℂ I, 𝓕 (fun w : EuclideanSpace ℂ I => ∏ i, f i (w i)) l = ∏ i, 𝓕 (f i) (l i) := by
  first | exact @GlobalTheory.fourier_prod_coord_complex | exact GlobalTheory.fourier_prod_coord_complex | (intros; apply GlobalTheory.fourier_prod_coord_complex <;> assumption)
