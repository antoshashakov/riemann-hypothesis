module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableSpecialFibreProperty
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.semistable_special_fibre_property : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (m r : ℕ), 1 ≤ r → r ≤ m → IsReduced ((MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) ⧸ Ideal.span {algebraMap O (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) ϖ}) := by
  first | exact @GlobalTheory.CompanionTheory.SemistableSpecial.special_fibre_isReduced | exact GlobalTheory.CompanionTheory.SemistableSpecial.special_fibre_isReduced | (intros; apply GlobalTheory.CompanionTheory.SemistableSpecial.special_fibre_isReduced <;> assumption)
