module

public import ReciprocityTheory.DualLattices.FischerAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantCoeffCayleyOperatorPowDeterminantPow
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph

@[expose] public section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

theorem _root_.GlobalTheory.T.constantCoeff_cayleyOperator_pow_determinant_pow : ∀ (p q : ℕ), constantCoeff ((cayOp p ℂ ^ q) (cayDet p ℂ ^ q)) = ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  first | exact @GlobalTheory.constantCoeff_cayOp_pow_cayDet_pow | exact GlobalTheory.constantCoeff_cayOp_pow_cayDet_pow | (intros; apply GlobalTheory.constantCoeff_cayOp_pow_cayDet_pow <;> assumption)
