module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionHeckeHolds
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.jacquet_projection_hecke_holds : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A2 G := by
  first | exact @GlobalTheory.CompanionTheory.Cass.jacquet_projection_hecke_intertwines | exact GlobalTheory.CompanionTheory.Cass.jacquet_projection_hecke_intertwines | (intros; apply GlobalTheory.CompanionTheory.Cass.jacquet_projection_hecke_intertwines <;> assumption)
