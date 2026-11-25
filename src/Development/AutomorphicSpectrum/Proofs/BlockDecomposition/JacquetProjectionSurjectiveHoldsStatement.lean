module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionSurjectiveHolds
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.jacquet_projection_surjective_holds : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π → ∀ t : D.T, D.IsStrDom t → ∀ U : Module.End ℂ (fixed π D.J), PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → ∀ w ∈ fixed (D.piN π) D.JT, ∃ v : fixed π D.J, D.proj π (v : V) = w := by
  first | exact @GlobalTheory.CompanionTheory.Cass.jacquet_projection_surjective | exact GlobalTheory.CompanionTheory.Cass.jacquet_projection_surjective | (intros; apply GlobalTheory.CompanionTheory.Cass.jacquet_projection_surjective <;> assumption)
