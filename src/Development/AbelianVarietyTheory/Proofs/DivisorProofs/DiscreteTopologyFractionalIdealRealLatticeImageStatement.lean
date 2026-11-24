module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyFractionalIdealRealLatticeImage
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

theorem _root_.GlobalTheory.T.discreteTopology_fractionalIdealRealLatticeImage : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), DiscreteTopology (latOf N) := by
  first | exact @GlobalTheory.LipschitzTR.discrete_latOf | exact GlobalTheory.LipschitzTR.discrete_latOf | (intros; apply GlobalTheory.LipschitzTR.discrete_latOf <;> assumption)
