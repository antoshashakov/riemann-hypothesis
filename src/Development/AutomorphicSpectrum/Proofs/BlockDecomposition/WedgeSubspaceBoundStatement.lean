module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeSubspaceBound
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.wedge_subspace_bound : WedgeSub := by
  first | exact @GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub | exact GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub | (intros; apply GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub <;> assumption)
