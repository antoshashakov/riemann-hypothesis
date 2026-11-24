module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleXSqAddOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraNormRatGaussianExtensionOfPair
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable

@[expose] public section

open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo


theorem _root_.GlobalTheory.T.algebraNorm_rat_gaussianExtensionOfPair : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (a b : F), ((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F (a, b)) : ℚ) : ℝ) = ∏ τ : F →+* ℝ, ((τ a) ^ 2 + (τ b) ^ 2) := by
  first | exact @GlobalTheory.GaussExt.norm_gEmb | exact GlobalTheory.GaussExt.norm_gEmb | (intros; apply GlobalTheory.GaussExt.norm_gEmb <;> assumption)
