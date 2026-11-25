module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FibreFactorHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularizedExponentialSum
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped Classical
namespace PositivityTheory.Rg.BcB.F

theorem _root_.GlobalTheory.T.regularized_exponential_sum : PositivityTheory.Rg.BcB.F.ExpSum := by
  first | exact @GlobalTheory.CompanionTheory.ExpSums.expSum_holds | exact GlobalTheory.CompanionTheory.ExpSums.expSum_holds | (intros; apply GlobalTheory.CompanionTheory.ExpSums.expSum_holds <;> assumption)
