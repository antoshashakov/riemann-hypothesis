module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityFinitePlaces
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.multiplicativity_finite_places : MulF := by
  first | exact @GlobalTheory.CompanionTheory.WedgeMinor.mulF | exact GlobalTheory.CompanionTheory.WedgeMinor.mulF | (intros; apply GlobalTheory.CompanionTheory.WedgeMinor.mulF <;> assumption)
