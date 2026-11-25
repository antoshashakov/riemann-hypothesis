module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph
public import ReciprocityTheory.DualLattices.FischerAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyOperatorPowEqSignedSumPartialDerivs
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

theorem _root_.GlobalTheory.T.cayleyOperator_pow_eq_signed_sum_partialDerivs : ∀ (p q : ℕ), cayOp p ℂ ^ q = ∑ τ : Fin q → Equiv.Perm (Fin p), sgnProd τ • dList (smallList τ) := by
  first | exact @GlobalTheory.CayleyBlock.cayOp_pow_eq_sum | exact GlobalTheory.CayleyBlock.cayOp_pow_eq_sum | (intros; apply GlobalTheory.CayleyBlock.cayOp_pow_eq_sum <;> assumption)
