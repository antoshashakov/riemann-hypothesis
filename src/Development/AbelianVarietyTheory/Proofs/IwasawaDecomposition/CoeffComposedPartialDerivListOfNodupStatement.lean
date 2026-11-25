module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffComposedPartialDerivListOfNodup
import Supplements.MathlibImports.AnalysisAndTactics
import ReciprocityTheory.DualLattices.FischerAdjointStatement

@[expose] public section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

theorem _root_.GlobalTheory.T.coeff_composedPartialDerivList_of_nodup : ∀ {σ : Type} [DecidableEq σ] (l : List σ), l.Nodup → ∀ (m : σ →₀ ℕ), (∀ v ∈ l, m v = 0) → ∀ (G : MvPolynomial σ ℂ), AddMonoidAlgebra.coeff (dList l G) m = AddMonoidAlgebra.coeff G (m + (l.map fun v => Finsupp.single v 1).sum) := by
  first | exact @GlobalTheory.CayleyBlock.coeff_dList_of_nodup | exact GlobalTheory.CayleyBlock.coeff_dList_of_nodup | (intros; apply GlobalTheory.CayleyBlock.coeff_dList_of_nodup <;> assumption)
