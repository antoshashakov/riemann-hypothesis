module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NrmCoeffProdLinear
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.nrm_coeff_prod_linear' : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ (v : Place k F) (m : ℕ) (α β : Fin m → F), nrm v (fun a : Fin (m + 1) => (∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).coeff a) = ∏ j, max (v.1 (α j)) (v.1 (β j)) := by
  first | exact @GlobalTheory.Nef.nrm_coeff_prod_linear | exact GlobalTheory.Nef.nrm_coeff_prod_linear | (intros; apply GlobalTheory.Nef.nrm_coeff_prod_linear <;> assumption)
