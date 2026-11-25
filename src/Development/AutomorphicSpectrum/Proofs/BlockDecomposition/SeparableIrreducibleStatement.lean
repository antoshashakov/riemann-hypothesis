module

public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableIrreducible
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open ReciprocityTheory.Ty.Fin

theorem _root_.GlobalTheory.T.separable_irreducible : ReciprocityTheory.Ty.Fin.St.SepIrr := by
  first | exact @GlobalTheory.CompanionTheory.FinRep.sepIrr | exact GlobalTheory.CompanionTheory.FinRep.sepIrr | (intros; apply GlobalTheory.CompanionTheory.FinRep.sepIrr <;> assumption)
