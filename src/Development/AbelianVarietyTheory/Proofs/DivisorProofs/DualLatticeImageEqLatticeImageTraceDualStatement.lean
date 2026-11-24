module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
public import Formalism.LatticeTheta.Statement
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeImageEqLatticeImageTraceDual
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent

@[expose] public section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

theorem _root_.GlobalTheory.T.dual_latticeImage_eq_latticeImage_traceDual : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → Formalism.H.dual (latOf N) = latOf (FractionalIdeal.dual ℤ ℚ N) := by
  first | exact @GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual | exact GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual | (intros; apply GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual <;> assumption)
