module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCompCoordDilationByHalfExp
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

theorem _root_.GlobalTheory.T.fourier_comp_coordDilationByHalfExp : ∀ (I : Type) [Fintype I] (f : EuclideanSpace ℂ I → ℂ) (y : I → ℝ) (l : EuclideanSpace ℂ I), 𝓕 (fun w : EuclideanSpace ℂ I => f (WithLp.toLp 2 (GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)))) l = (Real.exp (-∑ i, y i) : ℂ) * 𝓕 f (WithLp.toLp 2 (GlobalTheory.HeckeTheta.dil (-y) (WithLp.ofLp l))) := by
  first | exact @GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil | exact GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil | (intros; apply GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil <;> assumption)
