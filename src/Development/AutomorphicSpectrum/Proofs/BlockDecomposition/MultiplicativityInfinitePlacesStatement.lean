module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityInfinitePlaces
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.multiplicativity_infinite_places : DetMono → MulI := by
  first | exact @GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono | exact GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono | (intros; apply GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono <;> assumption)
