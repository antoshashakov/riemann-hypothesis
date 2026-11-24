module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSubquotients
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

theorem _root_.GlobalTheory.T.finite_subquotients :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      (ι : Type) [Fintype ι] [DecidableEq ι], PositivityTheory.Rg.BcN.F2.FinSubq F ι :=
  GlobalTheory.CompanionTheory.RepFinSubq.finSubq
