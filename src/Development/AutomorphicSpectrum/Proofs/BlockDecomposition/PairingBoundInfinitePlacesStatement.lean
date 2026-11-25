module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBoundInfinitePlaces
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.pairing_bound_infinite_places : DetMono → PairI := by
  first | exact @GlobalTheory.CompanionTheory.Wedge.pairI_of_detMono | exact GlobalTheory.CompanionTheory.Wedge.pairI_of_detMono | (intros; apply GlobalTheory.CompanionTheory.Wedge.pairI_of_detMono <;> assumption)
