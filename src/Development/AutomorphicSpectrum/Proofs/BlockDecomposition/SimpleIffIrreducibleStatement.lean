module

public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducible
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open ReciprocityTheory.Ty.Fin

theorem _root_.GlobalTheory.T.simple_iff_irreducible : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.simpleIffIrr | exact GlobalTheory.CompanionTheory.TyFin.simpleIffIrr | (intros; apply GlobalTheory.CompanionTheory.TyFin.simpleIffIrr <;> assumption)
