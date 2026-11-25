module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientNontrivialExistsMem
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.subquotient_nontrivial_exists_mem : ∀ {M W X : Type} [Group M] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ M W) (σ : Representation ℂ M X) (S T : Subrepresentation ρ), Nonempty ((subQuot S T).Equiv σ) → Nontrivial X → ∃ s ∈ S.toSubmodule, s ∉ T.toSubmodule := by
  first | exact @GlobalTheory.CompanionTheory.SubQuotNe.exists_mem_not_mem_of_subQuot_equiv | exact GlobalTheory.CompanionTheory.SubQuotNe.exists_mem_not_mem_of_subQuot_equiv | (intros; apply GlobalTheory.CompanionTheory.SubQuotNe.exists_mem_not_mem_of_subQuot_equiv <;> assumption)
