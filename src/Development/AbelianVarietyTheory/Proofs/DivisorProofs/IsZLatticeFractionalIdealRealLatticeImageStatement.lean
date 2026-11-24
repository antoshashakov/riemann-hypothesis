module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZLatticeFractionalIdealRealLatticeImage
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

theorem _root_.GlobalTheory.T.isZLattice_fractionalIdealRealLatticeImage : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → ∀ [DiscreteTopology (latOf N)], IsZLattice ℝ (latOf N) := by
  first | exact @GlobalTheory.LipschitzTR.isZLattice_latOf | exact GlobalTheory.LipschitzTR.isZLattice_latOf | (intros; apply GlobalTheory.LipschitzTR.isZLattice_latOf <;> assumption)
