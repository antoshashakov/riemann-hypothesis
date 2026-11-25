module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetLemmaHolds
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.jacquet_lemma_holds : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A4 G := by
  first | exact @GlobalTheory.CompanionTheory.Cass.sphericalProduct_A4 | exact GlobalTheory.CompanionTheory.Cass.sphericalProduct_A4 | (intros; apply GlobalTheory.CompanionTheory.Cass.sphericalProduct_A4 <;> assumption)
