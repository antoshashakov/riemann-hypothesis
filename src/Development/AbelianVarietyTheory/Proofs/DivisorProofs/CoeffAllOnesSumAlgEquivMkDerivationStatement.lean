module

public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAllOnesSumAlgEquivMkDerivation
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MvPolynomial

theorem _root_.GlobalTheory.T.coeff_allOnes_sumAlgEquiv_derivation_eq : ∀ {σ : Type} {L : ℕ} (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (b : MvPolynomial (Fin L ⊕ σ) ℂ), AddMonoidAlgebra.coeff (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (MvPolynomial.mkDerivation ℂ (Sum.elim (fun _ : Fin L => (0 : MvPolynomial (Fin L ⊕ σ) ℂ)) (fun v : σ => MvPolynomial.rename Sum.inr (D (MvPolynomial.X v)))) b)) (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ)) = D (AddMonoidAlgebra.coeff (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (b)) (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ))) := by
  first | exact @GlobalTheory.coeff_allOnes_sumAlgEquiv_mkDerivation | exact GlobalTheory.coeff_allOnes_sumAlgEquiv_mkDerivation | (intros; apply GlobalTheory.coeff_allOnes_sumAlgEquiv_mkDerivation <;> assumption)
